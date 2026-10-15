# Knowledge base

Living reference material for this repository. Two kinds of document:

* `papers/` — annotated notes on the external literature and code bases this project builds on
  or is measured against. Every note records the exact source (URL / arXiv id / commit) so a
  claim can be re-checked later.
* `sources/` — verbatim copies of third-party material (pinned so that expected results are
  never silently modified).
* `PROGRESS.md` — the phase-by-phase development log: what was implemented, verified,
  compiled and tested, with the actual commands and their output.

## Index

| Document | Contents |
|---|---|
| [papers/optisat.md](papers/optisat.md) | OptiSat / LambdaSat: the verified equality-saturation engine vendored into `quantum/` |
| [papers/equality-saturation-quantum.md](papers/equality-saturation-quantum.md) | Equality saturation and superoptimization for quantum circuits (Quartz, Sqale, PyZX, VOQC) |
| [papers/quantum-compiler-bugs.md](papers/quantum-compiler-bugs.md) | The documented numerical-soundness failures that drive `Quantum/BugRegression.lean` |
| [papers/ecdsa-fail.md](papers/ecdsa-fail.md) | arXiv:2609.09582 (ECDSA.Fail): the Q x T cost model and the circuit-optimization passes, mapped to what this repository implements |
| [papers/shor-verification.md](papers/shor-verification.md) | Formal verification of Shor's algorithm, RSA and ECDLP |
| [PROGRESS.md](PROGRESS.md) | Development log, build evidence, open obligations |

## Raw sources

* `sources/quantum-optimizer-bugs.README.md` — barghouthi/quantum-optimizer-bugs README
  (commit `8391022704cea125cb3b8f3ca64553b99c92f2b4`, branch `main`), large-angle bugs.
* `sources/quantum-optimizer-bugs.SMALL_ANGLES.md` — same repository, small-angle bugs.
* sources/arxiv-2609.09582.txt - the full text of arXiv:2609.09582v2 (ECDSA.Fail), stripped of markup.
* `../optisat_lean/` — clone of `lambdaclass/optisat_lean` at `f34ebd1` (its
  `ARCHITECTURE.md`, `BENCHMARKS.md` and insight notes are the reference for the vendored
  `quantum/LambdaSat`).
