# arXiv:2609.09582 - ECDSA.Fail: optimizing elliptic-curve point addition in Shor's algorithm

**Source (pinned).** https://arxiv.org/abs/2609.09582v2, "ECDSA.Fail: Open Autoresearch for
Optimizing Elliptic-Curve Point Addition in Shor's Algorithm" (Long, Pender, Huang, Santos,
Singh, Naskrecki, et al., 19 Sep 2026, CC BY 4.0). Full text archived in
[sources/arxiv-2609.09582.txt](../sources/arxiv-2609.09582.txt) (211k chars).

## The cost model (section 3.2)

Circuits are in the *kickmix* model with instruction set {X, Z, CNOT, CZ, SWAP, CCX, CCZ,
reset, HMR}; standalone Hadamards and reusable |+> preparation are excluded precisely because
CCX + H is universal and would defeat the efficient classical verifier. Two resources:

* **Q** - peak number of simultaneously live logical qubits;
* **T** - *average executed* Toffoli-equivalent count (each executed CCX/CCZ counts 1),
  averaging data-dependent firing probabilities over the evaluator's input distribution;
* score **S = Q x T**, lower is better; a separate low-Q track charts the (Q,T) Pareto frontier.

Best at cutoff: 1,151 qubits x 1,299,453 Toffoli ~ 1.496e9; a windowed-addition-compatible
variant: 1,162 x 1,684,161 with measured success p = 0.99809.

## The optimization techniques (section 5.3) and their status here

| # | Paper technique | Status in this repository |
|---|---|---|
| 5.3.1 | Jump-2 Euclidean algorithm in dialog-GCD | not implemented |
| 5.3.2 | Base-5 codec for the Jump-2 transcript | not implemented |
| 5.3.3 | Comparison-free ping-pong dialog-GCD (odd-preserving update) | not implemented |
| 5.3.4 | Karatsuba squaring with pseudo-Mersenne modulo | not implemented (secp256k1 p = 2^256 - 2^32 - 977) |
| 5.3.5 | Register-shared EEA and lane-lifetime refinement | partial: qubitWidth measures the live-qubit width actually used |
| 5.3.6 | **Constant propagation**: a block guarded by a known-0 classical bit is omitted - "an exact specialization, not an approximation" | **implemented and proved**: Quantum/Specialize.lean - cblock, condBlocks, constProp, denote_condBlocks (exact matrix equality), the ladder cost facts (ladder_saves), and cblock_phase, which proves classical control preserves phase equivalence in *both* branches (contrast Quantum/ControlPhase.lean, where quantum control does not) |
| 5.3.7 | **Dead-code / redundancy elimination**: "two adjacent applications of a self-inverse operation U cancel, U^2 = I, provided no intervening operation changes the relevant registers"; compute/uncompute annihilation | **implemented and proved**: Circuit.inv with denote_inv_mul / denote_mul_inv and the registered rules uncompute / uncompute2 (circuit level, not gate level), exercised by Example J (work ; work-dagger -> identity, 6 gates -> 0) |
| 3.2 | Q x T accounting | **implemented**: Quantum/Architecture.lean - Architecture (supported gate kinds + per-kind Toffoli cost), toffoliCount, qubitWidth, spacetimeScore, with qubitWidth_le, toffoliGates_append, supports_default, and clifford_refuses_crz showing an unsupported gate is *rejected*, not silently lowered |

## What is deliberately NOT copied

* The paper's Toffoli counts assume native CCX/CCZ. This gate library has no Toffoli primitive,
  so toffoliEquiv charges the two-qubit gates (CX, CZ, SWAP, CRZ) as the Toffoli-equivalent
  class, and that choice is a definition inside the artifact rather than a hidden assumption.
  Adding CCX/CCZ with an embed3 semantics is listed as open work.
* The paper's "average executed" Toffoli count is probabilistic over an input distribution. The
  formalized toffoliCount here is static; staticToffoli versus toffoliCount after constProp is
  the exact specialisation of the paper's idea for a *fixed* classical input, which is the only
  version that can be proved sound without a probability model.
* Retry/nonce-hunting success probabilities and leaderboard statistics are out of scope.
