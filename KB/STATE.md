# STATE — durable snapshot (authoritative; update every round)

## Environment (unchanged)
* Lean 4.26.0 + Mathlib v4.26.0 (rev 2df2f01); OptiSat/LambdaSat vendored at
  lambdaclass/optisat_lean@f34ebd1 under `quantum/LambdaSat/`.
* Every build needs `export ELAN_HOME=$PWD/.elan` from the repo root.
* Mathlib oleans + C objects are prebuilt in `quantum/.lake`: `lake build` = seconds.
* `timeout` does not exist on this macOS box; use the bash tool's own timeout.
* Lean stdout is block-buffered when redirected/piped: for progress of a long-running exe,
  write to a file with `IO.FS.withFile path Mode.append (fun h => h.putStrLn m)`.

## Green state (this round)
* `cd quantum && lake build` → "Build completed successfully (4447 jobs)", exit 0.
* `lake exe quantum` → 171 lines, exit 0 (`quantum/demo_output.txt`).
* `lake exe proptests` → "all metamorphic properties held"; 0 unaccepted certificates,
  0 mutated certificates wrongly accepted.
* `lake env lean Axioms.lean` → 27 theorems audited, only
  `propext, Classical.choice, Quot.sound`.  No `sorry`/`admit`/`native_decide`/project axioms.

## What changed this round (the big one)
1. `findDerivationBidir` fixed (`List.findSome?`, not `find?`) and wired into `optimizeFrom`.
2. New **cost-guided search** `costSearch` (+ `nodeLe`/`insertNode`/`mergeNodes`) that only
   follows cost-non-increasing steps; `findDerivationCost cfg c target` = costSearch, then
   bidirectional BFS.  `Correctness.lean` branch lemmas now state
   `findDerivationCost cfg c x = some/none`.
3. **Root cause of the old saturation hang found and fixed.**  The e-graph was being fed the
   *inverse* orientation of every cancelling rule (Z→S;S, Z→H;X;H, one→Z;Z, …).  Combined with
   both orientations of associativity this exploded: Example F reached **4448 classes after one
   round at fuel 3** and never finished a second round.  `quantumRules` now applies a
   **contracting bound**: an orientation is kept only if it does not increase the gate count
   (documented in the `quantumRules` docstring).  The old "occurs in the input" bound was
   dropped — it was too crude (it removed `Z;Z → one` from F, whose LHS only appears
   mid-derivation).
4. `Config.default` = fuel 8, maxIter 2, rebuildFuel 30, costFuel 60, maxSteps 10,
   searchBudget 400 — measured, not guessed.
5. Library pretty printer `Quantum.Gate.show` / `Quantum.Circuit.show` (Syntax.lean).
6. `Diag.lean` rewritten: `diag iso | sat | extract | all [fuel iter rebuildFuel]`, tracing to
   /tmp/diag_trace.txt.

## Measured pipeline (compiled, lake exe diag all 8 2 30)
| ex | input | saturated classes | extracted | cert steps | checker | search |
|----|-------|-------------------|-----------|-----------|---------|--------|
| E | 6g TTTTSS | 193 | Z;Z (2g, T 4→0) | 9 | ACCEPTS | 793 ms |
| F | 4g XZXZ | 29 | X;X (2g) | 4 | ACCEPTS | 550 ms |
| I | 3g CX X CX | 10 | X (1g, 2q 2→0) | 4 | ACCEPTS | 50 ms |
| H | 4g TTTT | — | Z (T 4→0) | 4 | ACCEPTS | 349 ms |
| J | 6g compute;uncompute | — | one | 1 | ACCEPTS | 5 ms |
The hand-built library certificates still go further: Examples.checkE takes TTTTSS to
identity in 8 steps, Examples.checkFG takes XZXZ to identity in 5 steps.

## Known traps (do not rediscover)
* The kernel does NOT reduce `Rat.add`/`Rat.mul`: `decide` fails on any proposition with an
  unevaluated angle sum.  Certificates containing angle sums must be proved through
  `step_of` / `walk_cons_ok` / `checkCertificate_of_walk`; angle equalities via
  `Angle.eq_of_components` + `norm_num`.
* Global phase is unsafe under quantum control (`crz_twoPi_not_phase_one`), safe under
  classical control (`cblock_phase`).
* Never add the reversed identity rules to `structRules` (numClasses grows forever).
* `List.get?` is not available; use `.drop i |>.head?`.  `IO.FS.appendText` does not exist.
* Embedding Lean text with backticks into JS template literals breaks; write files with
  `fs.writeFileSync` from arrays of single-quoted JS strings, or use heredocs.

## Remaining priorities
1. **Reach identity with the engine on E and F** (needs one more saturation round; the fix is a
   gate-kind closure filter so the rule set stays small enough for maxIter 4-6).
2. `Quantum/Invariants.lean`: instantiate OptiSat's invariant chain at `QOp n`/`PhaseOp n`
   (`empty_consistent`, `add_leaf_miss_consistent`, `merge_consistent`, `processClass_consistent`,
   `rebuildF_preserves_cv`, `applyRulesF_preserves_cv`, `saturateF_preserves_consistent`,
   `saturateF_preserves_wf`, `optimizeF_soundness_complete`) + initial-graph well-formedness.
   Spec §E.
3. Shor quantum half: modMul oracle as a permutation matrix proved equal to a circuit
   (×2 mod 3 on 2 qubits = SWAP), QFT₃ entrywise = DFT₃, then optimize with certificates.
4. Toffoli CCX/CCZ (3-qubit gate) so the ECDSA.Fail Q×T metric uses real gate costs.
5. README + theorem inventory refresh for the new search and the contracting bound.
