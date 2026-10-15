# Documented quantum-compiler correctness failures (regression drivers)

**Source (pinned).** `https://github.com/barghouthi/quantum-optimizer-bugs`, branch `main`,
commit `8391022704cea125cb3b8f3ca64553b99c92f2b4`. Verbatim copies in
[`../sources/`](../sources/quantum-optimizer-bugs.README.md).

Headline: *every* popular quantum SDK/optimiser tested mishandles rotation angles, changing
measurement probabilities from ≈0 % to ≈100 %.

| Tool | Input (gates execute left→right) | Cause | Wrong output |
|---|---|---|---|
| Qiskit 2.5.1 | `rz(1e17); rz(pi); rz(-1e17)` | fp addition: `1e17 + pi` rounds to `1e17` | identity |
| PennyLane 0.45.1 | same | same (`merge_rotations(atol=0)`) | identity |
| Cirq 1.7.0 | `rz(1e16*pi); rz(pi); rz(-1e16*pi)` | fp addition on exponents (`eject_z`) | identity |
| QuiZX 0.3.0 | `rz(2147483647*pi/4294967295); rz(2147483648*pi/4294967297)` | signed 64-bit overflow of the rational sum (denominators coprime, product `2^64-1`) | identity |
| tket 2.18.5 | `rz(pi); rz(-1e16*pi)` | angles stored in half-turns; `1 + (-1e16)` rounds | identity |
| BQSKit 1.2.1 | 2-qubit parameterised gate blocks | diagonal phase merged onto the **wrong qubit** (qubit-order remapping lost) | wrong 2-qubit circuit |
| Qrisp 0.9.9 | `rz(1e17); rz(pi); rz(-1e17)` | fp addition in gate fusion | identity |
| qBraid 0.12.1 / PyQASM 1.0.4 | `u3(0,1e17,0); rz(-1e17)` | fp addition inside the U3 decomposition (`phi + pi`) | Z instead of identity |
| CUDA-Q 0.16.0 | `rz(1e17); rz(pi); rz(-1e17)` | fp addition | identity |
| quilc 1.26.0 | same | fp addition | identity |
| MQT QMAP 3.10.0 | — | angle **silently dropped** | wrong circuit |

Small-angle variants (`SMALL_ANGLES.md`): tolerance-based deletion (`atol` 400× too large),
relative-tolerance commutation checks, PyZX phase-teleportation losing a sign, and qBraid
parsing `a/b*pi` as `a/(b*pi)` (operator-precedence bug).

## How this repository answers each failure mode

| Failure mode | Our counter-measure | Where |
|---|---|---|
| floating-point angle addition | `Angle := ℚ × ℚ` (rational + rational·π), exact `Rat` arithmetic; `val` is the only bridge to ℝ and is used only inside proofs | `Quantum/Angle.lean` |
| tolerance-based gate deletion | no tolerance anywhere; `Rz a ; Rz b → Rz (a+b)` requires *syntactic* angle equality of the sum, and `Rz 0 → I` only for the syntactic zero angle | `Quantum/Rewrites.lean` (`rz_add`, `rz_zero`) |
| integer overflow in phase sums | ℚ is arbitrary precision; regression test uses the QuiZX coefficients verbatim | `Quantum/BugRegression.lean` |
| global phase under control | `Rz 2π ≈ I` but `CRz 2π ≉ I` are both proved; contexts are sequential-composition only | `Quantum/ControlPhase.lean` |
| angle applied to wrong qubit | every certificate step carries explicit `Fin n` indices, the checker recomputes the lhs from them, and a wrong index makes the syntactic match fail | `Quantum/Certificates.lean` |
| silently dropped/unsupported gates | the checker looks rules up by stable id and rejects unknown ids; no lowering pass exists that could drop a gate | `Quantum/Rewrites.lean` (`findRule`) |
| unsound optimiser | the optimiser is untrusted; only an independently checked certificate is accepted, otherwise the input circuit is returned | `Quantum/Optimizer.lean` |
| operator precedence in angle literals | exact angle parser test: `(a/b)*π` parses, `a/(b*π)` is rejected | `Quantum/AngleParser.lean` |
