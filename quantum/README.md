# A proof-producing, formally verified quantum circuit optimizer in Lean 4

Deeply embedded, qubit-indexed quantum circuits; an independent matrix semantics over
`Matrix (Fin n → Bool) (Fin n → Bool) ℂ`; equivalence modulo global phase; a library of
machine-checked rewrites; a genuine equality-saturation engine (OptiSat) that proposes cheaper
circuits; and — the point of the whole exercise — an **independent, executable certificate
checker** whose soundness is proved, so a returned optimization carries a reproducible
mathematical justification rather than an appeal to the optimizer's own correctness.

```
untrusted optimizer                            trusted core
Rewrites → OptiSat e-graph → extraction  →  Certificate → checkCertificate → PhaseEquivalent
                                               (independent re-check of every step, position,
                                                side condition and endpoint)
```

Requires [elan](https://github.com/leanprover/elan). The package pins
`leanprover/lean4:v4.26.0` and Mathlib `v4.26.0` (rev `2df2f01`).

```sh
cd quantum
lake update                 # resolves Mathlib (pinned in lake-manifest.json)

# Strongly recommended: fetch Mathlib's prebuilt .oleans instead of compiling Mathlib.
mkdir -p .mathlibcache
MATHLIB_CACHE_DIR="$PWD/.mathlibcache" lake exe cache get

lake build                  # library + the quantum executable
lake exe quantum            # run every demonstration
lake exe quantum F          # run one demonstration (keys: A B C1 C2 D E F H I J K L N)
```

The first build of the executable also builds Mathlib's C objects (one-time, slow);
afterwards linking takes seconds.

## What is where

| Module | Contents |
|---|---|
| `Quantum/Angle.lean` | exact symbolic angles: `Angle := ℚ × ℚ` interpreted as `rat + piQ·π`; `eq_iff`, `eq_of_components`, `neg_neg`, `val_congr`. No floating point anywhere. |
| `Quantum/Syntax.lean` | `Gate n` (H, X, Y, Z, S, T, S†, T†, Rz, Rx, Ry, CX, CZ, SWAP, CRZ, CP) indexed by `Fin n`, two-qubit gates carrying distinctness proofs; `Circuit n = one | seq | gate`; `Gate.inv`, `Circuit.inv`, `gates`, `subcircuits`, `normalize`, decidable equality. |
| `Quantum/Gates.lean` | the 2×2 and 4×4 gate matrices, the exact eighth root `ω = (1+i)/√2` with `ω_mul_ω`, `normSq_ω`; identities `H2_mul_H2`, `S2_mul_S2`, `T2_mul_T2`, `X2_mul_Z2_phase`, …; unitarity `isUnitary_H2`, … |
| `Quantum/Embed.lean` | `embed1`/`embed2`: a gate matrix acting on chosen qubits inside an `n`-qubit register; `embed1_mul`, `embed2_mul`, `embed1_one`, `embed1_embed1_comm`, `embed1_embed2_comm`, `embed2_embed2_comm`. |
| `Quantum/Rotations.lean` | `Rz2`, `Rx2`, `Ry2`, `CRz4` with exact real-angle semantics: `Rz2_mul`, `Rz2_zero`, `Rz2_twoPi`, `Rz2_pi_Z2`, `CRz4_mul`, unitarity of all. |
| `Quantum/Semantics.lean` | `denote : Circuit n → Operator n` with `denote (seq a b) = denote b * denote a`; `denote_isUnitary`; `denote_gates`/`denote_normalize`; the specified actions `denote_x_action`, `denote_z_action`, `denote_cx_action`, `denote_swap_action`; the uncomputation laws `denote_inv_mul`, `denote_mul_inv`. |
| `Quantum/Equivalence.lean` | `PhaseEquivalent` (∃ unit-modulus λ with `denote a = λ • denote b`) and `EqExact`; `refl`, `symm`, `trans`, `pre`, `post`, `of_eqExact`, `phaseSetoid`. |
| `Quantum/Contexts.lean` | one-hole sequential contexts `Ctx`, `fill`, `comp`, contextual congruence `Ctx.congr` (phase) and `Ctx.congrEq` (exact). |
| `Quantum/Rewrites.lean` | the rule library: `Rule n` = stable id + lhs/rhs instantiation + decidable side condition + proved soundness; 37 rules (incl. cp_add, cp_zero, uncompute, uncompute2); `rules n`, `findRule`, `findRule_sound`. |
| `Quantum/Certificates.lean` | **the independent checker**: `Step`, `Certificate`, `stepTerms`, `applyStep`, `walk`, `checkCertificate`; `applyStep_sound`, `walk_some`, **`checkCertificate_sound`**; reflection helpers `step_of`, `step_none`, `walk_cons_ok`, `checkCertificate_of_walk`, `checkCertificate_none`. |
| `Quantum/Cost.lean` | `Cost` = (gateCount, twoQubitCount, tCount); `Cost.ofGate/of/ofGates`; `ofGates_append`, `of_gates`; lexicographic policy `CostConfig`, `Cost.le/lt`. |
| `Quantum/QuantumEGraph.lean` | OptiSat adapter: `QOp n` e-nodes, the phase quotient `PhaseOp n` with `pquot_op_mul_assoc`, `pquot_op_mul_one`, `pquot_op_one_mul`; the `NodeSemantics`, `Extractable`, `EvalExpr` instances; `extractableSound_qop`; `ofCircuit`. |
| `Quantum/Optimizer.lean` | schematic + instantiated rules (`quantumRules`, `structAssoc`, `structIdL`, `structIdR`, `toPatternSoundRuleFlip`), bounded saturation with two documented search-space bounds — the **contracting bound** (an orientation is kept only if it does not increase the gate count) and the **alphabet bound** `kindClosure` (a rule instance is kept only if its source side's gate kinds lie in the closure of the input's kinds) — then `saturateF` → `computeCostsF` → `extractAuto`; certificate synthesis (`oneStepRewrites`, `oneStepRewrites_apply`, `oneStepRewrites_sound`, `findDerivation`, `costSearch`, `findDerivationBidir`, `findDerivationCost`), the greedy baseline (`greedy`, `greedy_phaseEquivalent`), `Config`, `finish`, `round`, `rounds`, `optimizeFrom`, `optimize`. |
| `Quantum/Invariants.lean` | **the e-graph invariant chain instantiated at `QOp n`/`PhaseOp n`**: `Quadruple`, `addCircuit_uf_wf`, `ofCircuit_uf_wf`, `empty_quadruple`, `insert_preserves`, `merge_preserves`, `congruence_preserves`, `rebuild_preserves`, `saturation_preserves`, `addCircuit_quadruple`, `initial_quadruple`, `initial_bestNodeInv`, `optimizeF_eq`, `extraction_value`, `extraction_value_initial`, `saturation_preserves_initial`. |
| `Quantum/Correctness.lean` | `finish_spec`, `optimizeFrom_spec`, **`optimize_sound`**, `optimize_isSome`. |
| `Quantum/ControlPhase.lean` | why global phase may not be moved under a control: `rz_twoPi_phase_one`, `rz_twoPi_ne_one`, `crz_twoPi_not_phase_one`, `cz_cz_eq_one`. |
| `Shor/QFT.lean` | the quantum Fourier transform as a circuit in the verified language: `qft2` (Hadamards + controlled phases + reversal), `iqft2 = Circuit.inv qft2`, `qft2_unitary`, `qft2_inverse_exact` (exact, not merely up to phase), `cp_zero_certified` (accepted by the independent checker), `two_cphases` (CP(pi/2);CP(pi/2) = CP(pi), via exact rational arithmetic). | |
| `Quantum/Examples.lean` | the machine-checked examples A–J. |
| `Quantum/BugRegression.lean` | the adversarial suite (documented compiler bugs as theorems). |
| `LambdaSat/` | vendored OptiSat (see `KB/papers/optisat.md`); unmodified. |

## Theorem inventory

### A. Mathematical foundations
* primitive gate semantics: `H2 … SWAP4`, `Rz2`, `Rx2`, `Ry2`, `CRz4`, embedded by `embed1`/`embed2`.
* each primitive realizes its specified operation (not merely "is unitary"): `denote_x_action`, `denote_z_action`, `denote_cx_action`, `denote_swap_action`.
* primitive unitarity: `isUnitary_H2 … isUnitary_SWAP4`, `isUnitary_Rz2 … isUnitary_CRz4`; composition closure `isUnitaryM_mul`; every circuit: **`denote_isUnitary`**.
* composition semantics: `denote_seq`, `denote_ofGates`, `denote_gates`, `denote_normalize`.

### B. Equivalence
`PhaseEquivalent.refl/.symm/.trans/.pre/.post/.of_eqExact`, `phaseSetoid`; `EqExact` with the same six properties; contextual congruence over the whole supported context language: `Ctx.congr`, `Ctx.congrEq`. Controlled-subcircuit formation is deliberately inexpressible, and `ControlPhase.lean` proves why: `Rz(2π) ≈ I` but `CRz(2π) ≉ I` (`crz_twoPi_not_phase_one`).

### C. Rewrites
Each rule is a `Rule n` whose `sound` field proves `∀ args, side args = true → PhaseEquivalent (lhs args) (rhs args)`. The theorems: `rw_hh`, `rw_xx`, `rw_yy`, `rw_zz`, `rw_ss`, `rw_tt`, `rw_sDag_s`, `rw_s_sDag`, `rw_tDag_t`, `rw_t_tDag`, `rw_hXH`, `rw_hZH`, `rw_xz`, `rw_xy`, `rw_yz`, `rw_rz_add`, `rw_rz_zero`, `rw_rx_add`, `rw_rx_zero`, `rw_ry_add`, `rw_ry_zero`, `rw_rz_pi_z`, `rw_rz_halfPi_s`, `rw_rz_twoPi`, `rw_cxcx`, `rw_czcz`, `rw_swapswap`, `rw_crz_add`, `rw_crz_zero`, `rw_disjoint`, `rw_idL`, `rw_idR`, `rw_assoc`, `rw_uncompute`, `rw_uncompute2`. Lookup soundness: `findRule_sound`. Contextual rewriting: `Ctx.congr` via `applyStep_sound`. Phase-only identities: `rw_xz`, `rw_xy`, `rw_yz`, `rw_rz_twoPi`.

### D. Certificates
Single step: `applyStep_iff`, `applyStep_sound`, `applyStep_flip`. Derivation: `walk_nil`, `walk_cons`, `walk_some`. Checker: **`checkCertificate_sound`**. The checker imports only `Quantum.Rewrites` — never the e-graph, the optimizer, or extraction.

### E. E-graph,Restated for this domain in `Quantum/Invariants.lean`; each is the corresponding generic,OptiSat theorem applied to `QOp n` / `PhaseOp n` with the instances of,`Quantum/QuantumEGraph.lean`.,,* *Initial well-formedness*: `ofCircuit_uf_wf` (by induction over the circuit through,  `add_preserves_uf_wf`), `empty_quadruple`.,* *Node insertion preservation*: `insert_preserves` — adding an e-node preserves the whole,  bundle, extends the valuation pointwise on the classes that already existed, and the new,  class evaluates to the meaning of the node inserted.,* *Merge preservation* (class union and rule-based merge): `merge_preserves`.,* *Congruence closure correctness*: `congruence_preserves` (`processClass` is the congruence,  step; it preserves `ConsistentValuation` and `PostMergeInvariant`).,* *Rebuilding preservation*: `rebuild_preserves` (`rebuildF`, deferred congruence, run to a,  fuel bound, preserves the bundle with the same valuation).,* *Saturation preservation*: `saturation_preserves`, and `saturation_preserves_initial` for,  the graph the optimizer actually builds.,* *Semantic consistency of each class*: `addCircuit_quadruple` / `initial_quadruple` — the,  e-graph built from `c` carries a valuation whose value at the class of `c` is exactly,  `pquot (denote c)`.,,The circuit↔e-class bridge is `eval_patOf` + `pquot_phase`; the quantum-domain extraction,law is `extractableSound_qop`. Note that none of this is *trusted* by the end-to-end,theorem: `optimize_sound` runs on the external certificate checker alone.

### F. Extraction,Fuel-bounded `extractF`/`extractAuto` following `bestNode` pointers set by `computeCostsF`,with `egCostFn` (1 per primitive gate, 0 for identity and composition). General guarantees:,`extractF_correct`, `extractAuto_correct`, `extractAuto_complete`. Quantum instance:,`extractableSound_qop`.,,The pipeline the optimizer runs *is* OptiSat's `optimizeF` (`Invariants.optimizeF_eq`, by,`rfl`), so the generic pipeline theorem applies verbatim: `Invariants.extraction_value` and,its hypothesis-free corollary `Invariants.extraction_value_initial` say that if the,pipeline extracts `c'` from `c`, then `c'` evaluates — in the phase quotient, where,equality *is* equality up to global phase — to the value of the root e-class of the,saturated graph. `initial_bestNodeInv` discharges the cost-table side condition.,,Membership and minimum cost within the represented language are OptiSat's,`extractAuto_complete`/`extractF_correct`; the *bounded* nature of that language (depth and,node budget of the fuel-bounded enumeration) is a documented limit, and no theorem claims a,minimum over all mathematically equivalent circuits.

### G. End-to-end
**`Opt.optimize_sound`**: `optimize cfg c = some (c', cert) → checkCertificate c c' cert = true ∧ PhaseEquivalent c c'`. Also `Opt.optimize_isSome` (a result is always returned, and it is always checked — the fallback is the input circuit with the empty certificate) and `Opt.greedy_phaseEquivalent`.,,The body is `some (finish c (rounds cfg.rounds cfg c).1 (rounds cfg.rounds cfg c).2),(`optimizeFrom_eq`): `round` saturates, extracts and certifies; `rounds` repeats that,`cfg.rounds` times on the circuit the previous round produced and chains the certificates,with `++`. Because `walk` applies a certificate in list order, the concatenation is a,single derivation from the original input to the final output and a round boundary is not,a trust point — `optimizeFrom_spec` needs only `finish_spec`.

## Examples (kernel-checked in `Quantum/Examples.lean`)

| Key | Input | Output | Costs | Theorems |
|---|---|---|---|---|
| A | `H(0);H(0)` | identity | 2 → 0 gates | `checkA`, `soundA`, `costA` |
| B | `CNOT(0,1);CNOT(0,1)` | identity | 2 → 0 two-qubit | `checkB`, `soundB`, `costB` |
| C | `S;S` → `Z`; `T;T` → `S` | | 2 → 1 gates; T 2 → 0 | `checkC1`, `checkC2`, `tcountC2` |
| D | `X(0);Z(1)` ↔ `Z(1);X(0)` | cost-neutral | equal | `checkD`, `soundD`, `exactD` |
| E | `T;T;T;T;S;S` | identity | 6 → 0 gates, T 4 → 0 | `checkE`, `soundE`, `costE` |
| F/G | `X;Z;X;Z` | identity | 4 → 0 gates | `checkFG`, `soundFG`, `denotationFG`, `denotationFG_ne_one`, `fg_not_exact` |
| F′ | greedy baseline on `X Z X Z` | unchanged | 4 → 4 | `greedyStuckFG`, `greedyCostFG`, `greedySoundFG` |
| H | `T;T;T;T` | `Z` | T 4 → 0 | `checkH`, `soundH`, `costH_in`, `costH_out` |
| I | `CNOT(0,1);X(2);CNOT(0,1)` | `X(2)` | 2q 2 → 0 | `checkI`, `soundI`, `costI_in`, `costI_out` |
| J | `work ; work†` | identity, **exactly** | 3 → 0 | `checkJ`, `soundJ`, `exactJ` |

### What the live engine produces (`lake exe quantum`)

The table above is the *certificate library*: hand-built derivations that the checker
accepts, each with a theorem pinning it. The executable additionally runs the real
pipeline (saturate → extract → certify, `Config.rounds = 3` times) and prints the
greedy baseline next to it. Measured on this machine, compiled:

| Key | input | engine output | certificate | checker | time | greedy baseline |
|---|---|---|---|---|---|---|
| A | `H;H` | identity | 1 step | ACCEPTS | 1 ms | identity |
| B | `CX;CX` | identity | 1 step | ACCEPTS | 1 ms | identity |
| C1 | `S;S` | `Z` | 1 step | ACCEPTS | 1 ms | `Z` |
| C2 | `T;T` | `S` (T 2→0) | 1 step | ACCEPTS | 0 ms | `S` |
| D | `X(0);Z(1)` | unchanged (nothing cheaper exists) | 0 steps | ACCEPTS | 9 ms | unchanged |
| **E** | `T;T;T;T;S;S` | **identity** (6→0 gates, T 4→0) | **10 steps** | ACCEPTS | 764 ms | stuck at 5 gates |
| **F** | `X;Z;X;Z` | **identity** (4→0 gates) | **5 steps** | ACCEPTS | 383 ms | **stuck at 4 gates** |
| H | `T;T;T;T` | `Z` (T 4→0) | 4 steps | ACCEPTS | 291 ms | — |
| **I** | `CX(0,1);X(2);CX(0,1)` | `X(2)` (2q 2→0) | 4 steps | ACCEPTS | 49 ms | — |
| J | `work;work†` | identity | 1 step | ACCEPTS | 5 ms | — |

Example F is the specification's headline case: the explicitly defined greedy baseline
(only strictly cost-decreasing steps) cannot move at all, while the saturating engine
reaches identity through the cost-neutral `XZ ↔ ZX` commutation, and the 5-step
certificate of that derivation is accepted by the independent checker.
Example G is the required non-trivial global phase: `denotationFG` proves
`denote (X;Z;X;Z) = (-1) • 1`, `denotationFG_ne_one` proves it is not `1`, `fg_not_exact`
proves `¬ EqExact cFG one`, while `soundFG` proves `PhaseEquivalent cFG one`.

## Bug-regression suite (`Quantum/BugRegression.lean`)

| # | Documented bug | Our guarantee |
|---|---|---|
| 1 | `Rz(10^17);Rz(π);Rz(-10^17)` → identity (fp addition) | `angle_sum_exact`, `c1_fuses`, `c1_equiv_rz_pi`, `c1_to_z` |
| 2 | QuiZX overflow `rz(2147483647π/4294967295);rz(2147483648π/4294967297)` → identity | `qsum_ne_zero`, `q_fuse`, `q_sound` |
| 3 | `CRz(2π)` treated as identity | `crz_twoPi_certificate_rejected`, `crz_twoPi_not_id`, `crz_zero_ok` |
| 4 | angle applied to the wrong qubit (BQSKit) | `wire_permutation_rejected`, `cx_wire_order_rejected` |
| 5 | unsupported gate silently replaced | `unknown_rule_rejected`, `bogus_decomposition_rejected` |
| 6 | many small rotations deleted | `small_sum_exact`, `small_not_zero` |
| 7 | numerically close angles treated as inverses | `close_angles_distinct` |
| 8 | wrong phase sign / tampered arguments | `recomputed_lhs_not_trusted`, `wrong_position_rejected` |
| 9 | `a/b*pi` parsed as `a/(b*pi)` | exact `Angle` literals; `a/(b·π)` is inexpressible |
| 10 | CNOT control/target exchanged in the output | `cx_wire_order_rejected` |
| 11 | tampered extraction / unrelated cheaper output | `tampered_extraction_rejected`, `unrelated_cheaper_output_rejected` |
| 12 | cost-model drift | `cost_two_qubit`, `cost_tcount`, `cost_identity_zero`, `cost_additive` |
| 13 | unjustified merge / side condition ignored | `disjoint_side_condition` |
| 14 | broken chain, wrong endpoints, reordering | `reordered_rejected`, `missing_step_rejected`, `wrong_endpoint_rejected`, `wrong_start_rejected` |

## Trust boundary, honestly stated

**Trusted (kernel-checked):** the matrix semantics, the rewrite library and its soundness
proofs, the certificate checker and `checkCertificate_sound`, the end-to-end `optimize_sound`,
and the exact angle arithmetic.

**Untrusted:** OptiSat's saturation, e-matching, congruence, cost propagation and extraction;
the derivation searches (`costSearch`, `findDerivationBidir`, `findDerivationCost`), the round decomposition and certificate chaining (`round`, `rounds`); the greedy baseline. None of them can make a wrong
answer pass: `optimize` runs its own output through `checkCertificate` and falls back to the
input circuit with the empty certificate if the checker refuses.

**Outside the formal guarantee:**
* there is no OpenQASM parser/serializer here, so no parser correctness claim is made; angles
  are exact `⟨rat, piQ⟩` literals (`(a/b)*π` is representable, `a/(b·π)` is inexpressible,
  which is the strongest possible answer to the reported precedence bug);
* gate counts are abstract resource proxies, not hardware time, fidelity or physical cost;
* measurement, feedforward, ancilla reset and non-unitary channels are **not** in the circuit
  language, so no claim about them is made (the language cannot express them — fail closed);
* the probabilistic success analysis of sampling-based algorithms is not formalized here.

## Axiom audit

\`\`\`sh
lake env lean Axioms.lean
\`\`\`

prints the axioms behind the principal theorems. The project introduces no axioms of its own:
there is no \`sorry\`, \`admit\`, \`native_decide\`, \`partial\` or user-declared \`axiom\` anywhere
in \`Quantum/\` (check: \`grep -rn 'sorry\|admit\|axiom\|native_decide\|partial' Quantum/\`).

## Known limitations

1. Saturation is bounded three ways at once — fuel, rounds, and the two rule-set bounds (contracting,,   alphabet). A third saturation round still explodes the class count, which is why the optimizer,   re-runs the whole pipeline (`Config.rounds`) on the shrinking circuit instead of deepening a,   single pass. The bounds are documented in `quantumRules`/`kindClosure` and are search-space,   bounds, not semantic ones.,2. The live derivation search is slow on circuits with many rotation instances; the executable,   therefore uses a small budget and prints the library certificates for the deeper examples.
3. Angle rule instantiation is bounded by the angles occurring in the input (plus zero): a
   rewrite needing a fresh angle is not generated. A documented search-space bound, not a
   semantic one.
4. `decide` cannot evaluate rational arithmetic in the kernel (`Rat.add` does not reduce), so
   certificates containing unevaluated angle sums are proved accepted with `step_of` /
   `checkCertificate_of_walk` instead of `decide`.
