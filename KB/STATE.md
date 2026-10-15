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
* `cd quantum && lake build` → "Build completed successfully (4451 jobs)", exit 0.
* `lake exe quantum` → 209 lines, exit 0, 18 ACCEPTS + 5 negative-test REJECTS.
* `lake exe proptests` → all metamorphic properties held.
* `lake env lean Axioms.lean` → 49 theorems audited, only propext / Classical.choice / Quot.sound.

(older notes below)
* `cd quantum && lake build` → "Build completed successfully (4447 jobs)", exit 0.
* `lake exe quantum` → 183 lines, exit 0, 15 ACCEPTS + 5 negative-test REJECTS (`quantum/demo_output.txt`).
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

## Iterated rounds (the fix that made the engine actually win)
One saturation pass at maxIter 2 is cheap but shallow; a third round explodes.  So the
optimizer now runs the whole saturate-extract-certify pipeline `cfg.rounds` (default 3)
times, each time on the circuit the previous round extracted, and **chains the
certificates** (`p₁ ++ p₂ ++ …` — the checker walks the concatenation in one pass, so a
round boundary is not a trust point).  `optimizeFrom` is now
`some (finish c (rounds cfg.rounds cfg c).1 (rounds cfg.rounds cfg c).2)`, which also made
`Correctness.lean` much smaller (`optimizeFrom_eq` + `optimizeFrom_spec` by `subst`).
Also added: `kindClosure`/`kindsStep`/`kindsOf` — an **alphabet bound**: a rule instance is
generated only if its source side's gate kinds lie in the closure of the input's kinds
under the contracting orientations of the library (F: 1000+ instances → 16).

| ex | input | engine output | cert | checker | time | greedy baseline |
|----|-------|---------------|------|---------|------|-----------------|
| A | H;H | one | 1 | ACCEPTS | 1 ms | one |
| B | CX;CX | one | 1 | ACCEPTS | 1 ms | one |
| C1 | S;S | Z | 1 | ACCEPTS | 1 ms | Z |
| C2 | T;T | S (T 2→0) | 1 | ACCEPTS | 0 ms | S |
| D | X(0);Z(1) | unchanged (neutral) | 0 | ACCEPTS | 9 ms | unchanged |
| **E** | TTTTSS (6g, T4) | **one** (0g, T0) | **10** | ACCEPTS | 764 ms | TTTTZ (5g, T4) |
| **F** | XZXZ (4g) | **one** (0g) | **5** | ACCEPTS | 383 ms | **XZXZ (4g) — stuck** |
| H | TTTT | Z (T 4→0) | 4 | ACCEPTS | 291 ms | — |
| **I** | CX X CX (3g, 2q2) | X (1g, 2q0) | 4 | ACCEPTS | 49 ms | — |
| J | compute;uncompute (6g) | one | 1 | ACCEPTS | 5 ms | — |
Example F is the spec's headline: the explicitly defined greedy baseline (strictly
cost-decreasing steps only) cannot move, the saturating engine reaches identity.

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

## Round 6-7 additions
* **`Quantum/Invariants.lean` (NEW, 15 theorems)**: the whole §E chain instantiated at
  QOp n / PhaseOp n — `Quadruple`, `addCircuit_uf_wf`, `ofCircuit_uf_wf`, `empty_quadruple`,
  `insert_preserves`, `merge_preserves`, `congruence_preserves`, `rebuild_preserves`,
  `saturation_preserves`, `addCircuit_quadruple`, `initial_quadruple` (semantic consistency
  of the initial graph: the class of c has value pquot (denote c)), `addCircuit_bestNodeInv`,
  `initial_bestNodeInv`, `optimizeF_eq`, `extraction_value`, `extraction_value_initial`,
  `saturation_preserves_initial`.
* **`Shor/ModMul.lean` (NEW)**: the order-finding unitary for a=2, N=3 proved to BE SWAP.
  `val2` (little-endian), `modMul2_3`, `modMul2_3_val` (x↦2x mod 3 on group elements),
  `modMul2_3_fixes_three` (non-group state fixed, per the documented convention),
  `modMul2_3_involution`, `modMul2_3_bijective`, generic `permMat` + `permMat_mul` +
  `permMat_id` + `permMat_self_inverse` + `permMat_conjTranspose_self`,
  **`denote_swap_eq_permMat`** (entrywise, from the independent semantics),
  `isUnitaryM_permMat_modMul2_3` (inherited from denoteGate_isUnitary), `order_2_3`,
  **`unitary_order_eq_order`**, `denote_swap_pow_order`.
* **BUG FIXED: `anglesOf` did not list `Gate.cp`.**  Controlled-phase angles therefore never
  entered `candidateArgs`, so no `cp_add`/`cp_zero` instance with a non-zero angle was ever
  generated and CP fusion was impossible.  Symptom: `CP(pi/4);CP(pi/4)` optimized to
  itself.  After the fix the engine extracts `CP(pi/2)` with a 1-step accepted certificate.
  Lesson: when a gate is added to the syntax, every traversal in Optimizer.lean must be
  extended — `index1?/index2?`, `Gate.arity`, `Gate.mat2`, `anglesOf`, `gatesOf`.
* **Demo keys**: `quantum R` now also runs `demoShorOpt` (S1 QFT2;QFT2† → identity in 1
  certified step; S2 CP fusion; S3 the a=2,N=3 order-finding unitary squared → identity).
* `Config` gained `rounds : Nat := 3`; `Diag.lean` gained S1/S2 probes and rule-name tracing.

## Remaining priorities
1. ~~Reach identity with the engine on E and F~~ DONE (iterated rounds + alphabet bound).
   Next: make a single round deeper (the third round still explodes; look at OptiSat's
   rebuild cost with both assoc orientations present).
2. `Quantum/Invariants.lean`: instantiate OptiSat's invariant chain at `QOp n`/`PhaseOp n`
   (`empty_consistent`, `add_leaf_miss_consistent`, `merge_consistent`, `processClass_consistent`,
   `rebuildF_preserves_cv`, `applyRulesF_preserves_cv`, `saturateF_preserves_consistent`,
   `saturateF_preserves_wf`, `optimizeF_soundness_complete`) + initial-graph well-formedness.
   Spec §E.
3. Shor quantum half: modMul oracle as a permutation matrix proved equal to a circuit
   (×2 mod 3 on 2 qubits = SWAP), QFT₃ entrywise = DFT₃, then optimize with certificates.
4. Toffoli CCX/CCZ (3-qubit gate) so the ECDSA.Fail Q×T metric uses real gate costs.
5. README + theorem inventory refresh for the new search and the contracting bound.
