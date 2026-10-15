# STATE — compact project snapshot (authoritative, updated each round)

Read this first after any context compaction. Details: [README.md](../README.md),
[quantum/README.md](../quantum/README.md), [PROGRESS.md](PROGRESS.md).

## Environment (must be reproduced exactly)

* Repo root: `/Users/julian/Downloads/formally_verified` (macOS, 10 cores, 32 GB).
* **Every lake/lean command needs** `export ELAN_HOME=$PWD/.elan` from the repo root — the
  global `~/.elan` is not writable from this session. The workspace elan holds
  `leanprover--lean4---v4.26.0`.
* Package `quantum/`: Lean `v4.26.0`, Mathlib `v4.26.0` (rev `2df2f01`). Mathlib .oleans are
  built in `quantum/.lake`; Mathlib C objects are built too, so exe linking is fast.
* `optisat_lean/` = clone of lambdaclass/optisat_lean @ `f34ebd1`; vendored verbatim into
  `quantum/LambdaSat/` (verify with `diff -rq quantum/LambdaSat optisat_lean/LambdaSat`).
* Long commands: run with `run_in_background: true` and poll — the bash tool promotes calls that
  exceed ~60 s and `run_code` has its own 120 s default (pass `timeoutMs`).
* Lean string literals: no `\\u{...}` escapes; use plain characters.

## Build / test commands and last recorded results

| Command (from repo root) | Last result |
|---|---|
| `cd quantum && lake build` | **Build completed successfully (4447 jobs)**, exit 0 |
| `cd quantum && lake env lean Axioms.lean` | every principal theorem: only `propext, Classical.choice, Quot.sound` |
| `cd quantum && lake exe quantum` | 138 lines, exit 0 → captured in `quantum/demo_output.txt` |
| `cd quantum && lake exe proptests` | 12 circuits, 39 accepted rewrites, 0 failures, mutations all rejected |
| `cd quantum && lake exe diag` | **running / unfinished** (pipeline diagnostics, round 3) |
| grep for `sorry\|admit\|native_decide\|partial def\|^axiom` in Quantum/ Shor/ Main.lean PropertyTests.lean | clean (prose only) |

## Module map (quantum/)

* Semantics core: `Angle` (exact ℚ+ℚπ angles), `Syntax` (Gate/Circuit, `Gate.inv`,
  `Circuit.inv`), `Gates` (2×2/4×4 matrices, ω), `Embed` (`embed1`/`embed2`/`embedList` +
  commutation), `Rotations` (Rz/Rx/Ry/CRz/**CP4**), `Semantics` (`denote`, unitarity,
  specified actions, `denote_inv_mul`), `Equivalence` (`PhaseEquivalent`, `EqExact`),
  `Contexts` (`Ctx.congr`, `Ctx.conjEq`).
* Trusted boundary: `Rewrites` (**37 rules**, incl. `uncompute`/`uncompute2`, `cp_add`,
  `cp_zero`, `crz_zero`), `Certificates` (`checkCertificate`, `checkCertificate_sound`,
  reflection helpers `step_of`/`walk_cons_ok`/`checkCertificate_of_walk`/`checkCertificate_none`).
* Untrusted optimizer: `QuantumEGraph` (OptiSat adapter, `extractableSound_qop`), `Optimizer`
  (schematic + instantiated rules, `saturateF`→`computeCostsF`→`extractAuto`, `greedy`,
  `findDerivation`, `finish`, `optimize`), `Correctness` (**`optimize_sound`**,
  `optimize_isSome`), `Cost`, `Architecture` (Q×T accounting), `Specialize` (constant
  propagation), `ControlPhase` (why phase ≠ safe under control), `Examples` (A–J),
  `BugRegression` (compiler-bug fixtures).
* Shor: `Shor/Arith` (`modExp`, `order`, **`order_dvd`**, CRT), `Shor/RSA`
  (**`shor_factor`**, `factor_15`, `factor_21`, `rsa_roundtrip_33`), `Shor/ECDLP`
  (`recovery`, `recovered_7`), `Shor/QFT` (`qft2`, `iqft2`, `qft2_inverse_exact`,
  `cp_zero_certified`, `two_cphases`).
* Exes: `quantum` (demo, keys A B C1 C2 D E F H I J K L N P R), `proptests`, `diag`.

## Known traps (do not rediscover)

* **The kernel does not reduce `Rat.add`/`Rat.mul`.** Any `decide` on a proposition containing
  an unevaluated angle sum fails. Prove such certificates with `step_of` + `walk_cons_ok` +
  `checkCertificate_of_walk` (syntactic matching), and angle equalities with
  `Angle.eq_of_components` + `norm_num`.
* OptiSat saturation **must not** include the reversed identity rules (inserting `one`): they
  make `numClasses` grow every round and `saturateF` never stabilises. Assoc is supplied in both
  orientations only.
* `Quantum/Optimizer.lean` lives in `namespace Quantum.Opt`; `QOp`/`PhaseOp` in `Quantum.EG`;
  `oneHot`/`zeroB` in `Quantum.ControlPhase`.
* Reserved identifiers that bit us: `end` as a binder, `at` as a `let` name, `;` is
  `Circuit.seq` after `open Quantum` (never use `;` as a do-block separator in Main).
* `IO.FS.writeToFile`/`appendToFile` do not exist in 4.26; use `IO.FS.withFile … (fun h =>
  h.putStrLn s)`. `List.getD` takes the default first; prefer `headD`.

## Open work, in priority order

1. **Live-search quality/performance.** `optimize` falls back to the input on the multi-step
   examples (E, F, I) because `findDerivation` (BFS, budget 4000) cannot find the derivation and
   `oneStepRewrites` is expensive. `lake exe diag` (Diag.lean) is the instrument to decide
   whether extraction or the derivation search is the bottleneck. Fix candidates: index rule
   instances by matched subcircuit; bidirectional/iterative-deepening derivation search; or
   reconstruct derivations from e-graph cost pointers (needs provenance OptiSat lacks).
2. **E-graph invariants for the quantum domain** (spec §7/§E): instantiate OptiSat's
   `ConsistentValuation`/`PostMergeInvariant`/`SemanticHashconsInv`/`HashconsChildrenBounded`
   chain for `QOp`/`PhaseOp` and state "every term in a class is phase-equivalent".
3. **Shor quantum half**: entrywise QFT = DFT (pin the `Fintype (Basis n)` bit convention),
   modular-multiplication / EC point-addition oracles as circuits, then run the optimizer over
   them with certificates.
4. **Toffoli CCX/CCZ** via `embedList` on a 3-element index list, so the Q×T accounting can use
   the paper's own gate costs.
5. Optional: exact-angle parser with precedence tests (§D), approximate mode with error budget (§B).

## Commits so far

`186fdfd…` Merkle → `5364e8a` Dijkstra → `ae4b459` Quantum semantics/rewrites/checker →
`8d8ff9d` green library build + optimize_sound + BugRegression → `f423bc8` README + audit →
`8642ccc` saturation fix + demo → `9942eb9` ECDSA.Fail passes + Shor core → `3f2c7b3` CP gate +
Shor/QFT → `98dc295` proptests → `1fca333` round-2 close.
