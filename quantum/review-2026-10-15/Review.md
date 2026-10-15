# Quantum project review — 15 October 2026

The strongest part of this project is its independent, proved-sound rewrite certificate checker. I found no counterexample to that checker or the public optimizer's semantic soundness theorem. There are implementation bugs and substantial gaps between some theorem statements and their advertised meaning. The evidence supports a verified rewrite-checking prototype, with small working optimization examples; it does not establish a competitive optimizer or verified Shor computation.

This reviews the working tree, including changes made to `Main.lean` and `Quantum/Optimizer.lean` while the review was running. The final `lake build` passed. I changed no implementation or existing proof files; this directory contains the review and additional checks. The Git HEAD was `59eca9e2233fb9b898de1a1bb9d5ce8738d50372`; the reviewed tree includes uncommitted changes. `source-hashes.txt` identifies the main audited files.

## What it achieves

Circuits are a typed syntax with finite qubit indices, exact angles, and distinctness proofs for two-qubit gates. Their reference semantics is a complex matrix, with ordinary gate matrices and the correct execution-order convention. A library of proved identities permits replacement inside sequential contexts. Equality saturation proposes a candidate, a separate search reconstructs a rewrite derivation, and the independent checker validates the entire chain and both endpoints. A failed check returns the input circuit.

The main contract is:

```text
optimize cfg c = some (c', cert)
  ⇒ checkCertificate c c' cert = true
    ∧ ∃ λ, normSq λ = 1 ∧ denote c = λ • denote c'
```

That is a substantive all-input semantic preservation guarantee. It is compatible with returning the original input on every run. It does not assert improvement, minimum cost, architectural implementability, or useful runtime. Finite fuel proves mathematical termination, not a practical time or memory bound.

The checker is structurally independent of the e-graph and extraction. Its dependency direction, reconstruction of rule terms, checks of side conditions and contexts, and endpoint equality are appropriate. The gate definitions I inspected use the expected H, Pauli, S/T, rotation, CNOT, CZ, SWAP, CRz and CP conventions. The explicit restriction on controlled subcircuits is sound: global phase equivalence cannot generally be lifted under quantum control. The matrix semantics is symbolic in the proofs; the executable checker does not enumerate a 2^n-dimensional matrix.

## Findings

### 1. [P1] The internal extraction theorem's conclusion is vacuous

Location: [Quantum/Invariants.lean:168](/Users/julian/Downloads/formally_verified/quantum/Quantum/Invariants.lean:168), also `extraction_value_initial` and the corresponding vendored pipeline statements.

The conclusion is `∃ v_sat, eval c' = v_sat root`. Nothing in that conclusion constrains `v_sat` to be consistent with the saturated graph or to preserve the initial input's meaning. It is true for any proposed output, without performing extraction: choose `v_sat := fun _ => eval c'`. `Checks.lean` proves the exact conclusion with the extraction hypothesis removed, using `⟨fun _ => eval c', rfl⟩`.

The existing proof may construct a meaningful valuation internally, but its public statement discards the properties that make the witness meaningful. It consequently cannot establish preservation of the input's value. This does not invalidate `optimize_sound`, which uses the separate checker.

Repair: retain consistency and preservation of the original root value in the existential package, and derive an explicit `PhaseEquivalent c c'` theorem for successful raw extraction.

Related overclaim: the README attributes minimum-cost guarantees to `extractF_correct` and `extractAuto_complete`. The former proves semantic equality; the latter proves conditional success, not optimality. Its reconstruction hypothesis quantifies over *every* child list, including malformed ones. For QOp, reconstructing `.seq 0 1` from `[]` fails; this is checked in `Checks.lean`. The positive-cost acyclicity theorem also cannot directly apply to `egCostFn`, whose identity and sequence costs are zero. No applicable bounded optimality theorem has been established by these references.

### 2. [P1] ECDLP's advertised measured-pair recovery uses the wrong relation

Location: [Shor/ECDLP.lean:4](/Users/julian/Downloads/formally_verified/quantum/Shor/ECDLP.lean:4) and `recovery` at line 25.

For the documented map `f(a,b)=aP+bQ`, `Q=kP`, period vectors satisfy `a+k b=0`. Fourier samples lie in the annihilator of that subgroup: raw samples `(u,v)` satisfy `v=k u`, and recovery uses `v/u` when `u` is invertible. The module instead calls a period vector a measured pair and uses `-c/d`. This distinction is derived explicitly in [Proos and Zalka, §2.2.3–2.2.4](https://arxiv.org/html/quant-ph/0301141v1#S2.SS2).

Example: for secret 5 modulo 7, `(u,v)=(1,5)` satisfies the Fourier relation. The advertised formula returns `-1/5=4`. The modular arithmetic is kernel-checked in `Checks.lean`. The theorem itself is correct under its stated hypothesis `c+d*k=0`; the problem is identifying that hypothesis with the raw measurement.

Repair: distinguish Fourier samples from period vectors. Either prove recovery from `v=k*u`, or explicitly convert `(u,v)` to the period vector `(-v,u)` before applying the existing lemma. There is currently no formal measurement-to-hypothesis bridge and no elliptic-curve point computation in this module.

### 3. [P2] Nested rewrite contexts are composed in the wrong order

Location: [Quantum/Optimizer.lean:377](/Users/julian/Downloads/formally_verified/quantum/Quantum/Optimizer.lean:377).

`allContextsFrom` wraps the accumulated outer context with the new local frame. For a path deeper than one frame, the required operation is to compose the local frame *inside* the outer context. The present code reverses prefixes or changes association.

Reproduction: on `Z ; (X ; (H ; H))`, the checker accepts an `hh` step in context `seqL Z (seqL X hole)`, producing `Z ; (X ; one)`. Yet `oneStepRewrites` does not enumerate that result. Both facts are proved by `decide` in `Checks.lean`.

Impact: valid local reductions are missed, certificate search needs unnecessary structural detours, and bounded search can discard usable extracted circuits. The independent checker prevents this bug from accepting a semantically wrong rewrite.

Repair: extend contexts using `Ctx.comp k (Ctx.seqR Ctx.hole b)` and `Ctx.comp k (Ctx.seqL a Ctx.hole)`. Add a completeness property relating enumerated contexts to tree positions, not only the existing soundness filter.

### 4. [P2] The declared Clifford target accepts non-Clifford rotations

Location: [Quantum/Architecture.lean:61](/Users/julian/Downloads/formally_verified/quantum/Quantum/Architecture.lean:61).

The whitelist rejects T/T† and controlled rotations but admits every Rz, Rx and Ry. In particular, it accepts `Rz(pi/4)`, which is T up to global phase. The acceptance is kernel-checked in `Checks.lean`. A gate-kind-only predicate cannot distinguish Clifford rotation angles from arbitrary angles.

The comment that rewrites can never introduce unsupported gates is also false for arbitrary `Architecture`: an architecture supporting only Rz accepts the input `Rz(pi)`, while the certified `rz_pi_z` rewrite produces unsupported Z. This is separately checked. Architecture is not an input to the optimizer, and architecture support is not enforced at its return boundary. `supports_default` proves only that an all-true whitelist accepts everything.

Repair: make support depend on the full gate, and explicitly check or prove support preservation for a selected target.

### 5. [P2] Status reporting exceeds the optimization budget and stalls a tiny demo

Location: [Quantum/Optimizer.lean:748](/Users/julian/Downloads/formally_verified/quantum/Quantum/Optimizer.lean:748) and [Main.lean:80](/Users/julian/Downloads/formally_verified/quantum/Main.lean:80).

`saturationStatus` reruns saturation twice from the original circuit, once at `maxIter` and once at `maxIter+1`. The latter goes beyond the user's bound, into the deeper pass the README already identifies as explosive. The displayed optimization time excludes these extra runs.

On the final built executable, Example F produced a checked 5-step certificate reducing 4 gates to 0 in 634 ms, then blocked before printing saturation status. A separate capped run of the executable timed out after 15.01 seconds. The earlier executable without this diagnostic completed the same example in 727 ms.

Equal class/node counts are also only a bounded observation, not a semantic fixed-point proof: with zero matching fuel, HH reports `fixedPoint` even though the available HH rewrite applies. That runtime observation is reproduced in `Checks.lean`; the code's explanatory comment partially acknowledges this limitation.

Repair: collect change and budget information during the actual run; do not deepen saturation solely to label the result. Use an unknown/budget-limited status when the bounds prevent a meaningful fixed-point test.

### 6. [P2] The property harness does not test the normal optimizer or determinism

Location: [PropertyTests.lean:74](/Users/julian/Downloads/formally_verified/quantum/PropertyTests.lean:74), duplicated in `Tools/PropertyTests.lean`.

`testCfg` is unused. The only end-to-end optimization invocation uses zero search budget and zero saturation iterations. The `nondet` field counts acceptance of an empty reflexive certificate; it never compares repeated executions. The `improved` field counts proposed rewrite steps, not improvements. Step soundness is checked after `oneStepRewrites` has already filtered through the same checker, so it cannot detect missing steps such as finding 3. There is no independent matrix differential test. Failure prints a message but does not return a failing process exit status.

The existing run passes on 12 generated circuits, but that is much narrower evidence than the opening description promises.

Repair: exercise nonzero budgets, compare repeated outputs, assert actual costs, test enumeration completeness against a separate traversal, and return a nonzero status on failure.

## Limits on the Shor and resource claims

`qft2_unitary` and `qft2_inverse_exact` instantiate generic results true of any circuit and its syntactic inverse. The module explicitly leaves identification with the Fourier matrix unproved. Its introductory normalization `omega^(x*y)/2^m` should be `omega^(x*y)/sqrt(2^m)` for an m-qubit unitary DFT. The inverse theorem therefore does not establish QFT functionality.

`ModMul` genuinely identifies SWAP with multiplication by 2 modulo 3 under a specified encoding. However, `unitary_order_eq_order` proves only `U^r=I`, not that r is the least positive unitary exponent. There is no general modular multiplication, controlled-power/phase-estimation implementation, measurement model, continued-fraction recovery, or quantum sampling success proof. The factoring examples compute tiny orders classically by exhaustive enumeration through the totient bound. `modExp` constructs `a^e` before reducing it. These are specifications and small examples, not scalable arithmetic implementations.

The resource definitions are internally checkable but do not reproduce the cited benchmark's quantities. Here CX/CZ/SWAP/CRz/CP each cost one "Toffoli-equivalent", and single-qubit T costs zero. `qubitWidth` counts touched wire labels; the language has no allocation or lifetime model. The cited benchmark counts executed CCX/CCZ, averages over its evaluation distribution, and measures peak live logical width. Its instruction set also differs. Thus the project's score cannot support comparisons to that benchmark. See [ECDSA.Fail, §3.2](https://arxiv.org/html/2609.09582v1#S3.SS2).

The constant-propagation pass correctly handles an externally supplied Bool guard. But `cblock false c` already denotes identity and already costs zero before `constProp`. I proved that source and specialized gate counts are equal for every such block list. The reported strict saving compares against a separate static sum that charges for all guarded blocks. The sample named a double-and-add ladder is a list of arbitrary CX/X/H gates, with no proved multiplication specification. This is a valid small specialization lemma, not verified elliptic-curve arithmetic.

## Usefulness and next steps

The checker is worth preserving. It can give arbitrary optimizer experiments a precise semantic acceptance boundary, and exact rational-plus-pi angles avoid rounding and fixed-width-overflow failure modes. Its most plausible useful role is as a certifying backend for transformations generated elsewhere.

The case for the present search engine is weak. The examples are small, the greedy baseline forbids even neutral reassociation, and the certificate is rediscovered through a second bounded search rather than extracted from e-graph explanations. Candidate generation enumerates all register qubit pairs, angle pairs and input gate pairs; a node budget does not bound that enumeration. There are no realistic circuit-family benchmarks establishing scaling or advantage over serious optimizers.

Verified quantum optimization already has substantial prior art in [VOQC](https://arxiv.org/abs/1912.02250), while [Quartz](https://arxiv.org/abs/2204.09033) explores automatically generated circuit transformations. A Lean certificate checker combined with equality saturation could be a useful contribution, but this repository has not demonstrated a practical advantage over those approaches.

I would first repair the context traversal, theorem statements, target predicate, reporting and test harness. Then retain e-graph explanation edges to generate certificates directly, add one real circuit interchange path with a clear trust boundary, and benchmark useful circuit families against a baseline that includes neutral rewrites. Strengthen the public contract with a checked cost-nonincreasing condition under the selected policy. The present `costConfig` affects certificate-search ordering; extraction still uses gate count alone.

For Shor work, choose a functional milestone: prove a parameterized QFT equals its Fourier specification, or implement a general clean reversible arithmetic block and prove its action. More tiny identity and inverse examples will not resolve the missing functional guarantees.

## Verification evidence

- Final `lake build`: passed, 4451 jobs, with linter warnings.
- `lake env lean Axioms.lean`: passed; the 47 principal declarations list only `propext`, `Classical.choice`, `Quot.sound`, or subsets/none. No `sorryAx` appeared.
- Source scan found no proof holes or custom axiom declarations in Quantum/Shor. Vendored LambdaSat contains partial execution helpers; these are separate from the total public quantum pipeline.
- Existing property harness: passed, 12 circuits, 39 accepted one-step rewrites, 12 rejected mutations. Its limitations are finding 6.
- `lake env lean --run review-2026-10-15/Checks.lean`: added kernel-checked reproductions and one explicitly executable saturation-status observation.
- Example F: checked 4→0 gate optimization observed; final CLI timed out in the newly added diagnostic as described above.

Logs and the reproducible check file are saved beside this review. The Mathlib/proofwidgets working copies have local build-configuration edits; Mathlib's inspected edit removes a ProofWidgets build guard, not a logical axiom. This was an incremental local build and audit, not a clean-room reproducibility build or independent Lean-kernel implementation audit.
