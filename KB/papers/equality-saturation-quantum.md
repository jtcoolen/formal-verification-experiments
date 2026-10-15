# Equality saturation / superoptimization for quantum circuits

* **Quartz** — *Quartz: Superoptimization of Quantum Circuits*, PLDI 2022.
  <https://arxiv.org/abs/2204.09033>, <https://www.cs.cmu.edu/~zhihaoj2/papers/quartz-pldi22.pdf>.
  Exhaustive search over equivalent circuits using e-graphs + SMT; discovers rewrite rules
  automatically. Motivation for our Example F: greedy peephole passes miss circuits whose
  simplification needs a cost-neutral step.
* **Equality saturation for quantum circuit optimization** (PACMPL/TOPLAS 2025),
  <https://dl.acm.org/doi/10.1145/3808254>. Scheduled equality saturation; ablations show the
  benefit of keeping cost-neutral and cost-increasing rewrites during saturation rather than
  only cost-decreasing ones — exactly the behaviour our `assoc`/`xz` steps exhibit in
  Example F/G.
* **VOQC** — *A Verified Optimizer for Quantum Circuits*, POPL 2021 (Hietala, Rand, Wu,
  Hicks). <https://arxiv.org/abs/1912.02250>. Coq-deeply-embedded circuits, verified
  rewrites with respect to a matrix semantics. Closest prior art to our Phase 1–2: the
  difference is that VOQC verifies the *transformations* inside Coq, while we verify an
  independent *certificate checker* and let an unverified e-graph engine propose circuits.
* **PyZX** — *PyZX: Large Scale Automated Diagrammatic Reasoning*, QCE 2019,
  <https://arxiv.org/abs/1904.04735>. ZX-calculus rewriting; not formally verified, and its
  0.9.0 release is one of the tools with a documented small-angle sign bug (see
  quantum-compiler-bugs.md).
* **Synthesis of Compact and Expressive Quantum-Circuit Optimizations**, TOPLAS 2026,
  <https://dl.acm.org/doi/10.1145/3839450> — rule synthesis with soundness-by-validation and
  bounded completeness; supports our choice of "bounded optimality inside an explicit finite
  extraction space" instead of claiming global optimality.

## Notes for our design

* Global phase: every quantum rewriter that supports `≈` (phase equivalence) must refuse to
  move a phase-equivalent subcircuit under a control. Our `Ctx` language is deliberately
  sequential-composition-only; see `quantum/Quantum/ControlPhase.lean`.
* Cost model: gate count / two-qubit count / T count are *abstract* counts. Quartz and the
  TOPLAS'25 scheduled-e-sat paper both optimise proxy costs, not fidelity; we state the same
  limitation in `quantum/Quantum/Cost.lean`.
