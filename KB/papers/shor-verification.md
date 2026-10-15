# Formal verification of Shor's algorithm, RSA and ECDLP

Prior art:

* **SQIR / Quilp / VOQC** — <https://arxiv.org/abs/1912.02250> and the SQIR library
  (<https://github.com/microsoft/Quilp>): Coq formalisation of Shor's factorisation with a
  certified end-to-end implementation (Rand et al., *A Formally Certified End-to-End
  Implementation of Shor's Factorization Algorithm*, <https://arxiv.org/abs/2204.07112>).
  The quantum part is verified as a *circuit*; the classical post-processing (order finding,
  continued fractions) is verified separately in Coq.
* **Foundations of a quantum library in Lean** — Mathlib has `Matrix`, `Unitary`,
  `ZMod`, `Nat.ModEq`, continued fractions (`Mathlib/NumberTheory/ContinuedFractions`) and
  `Nat.gcd`/`xgcd` machinery, which is what we build the Lean version on.
* **ECDLP**: no complete formally-verified Shor-for-ECDLP exists in the literature; the
  standard reference for the classical group law is IEEE P1363 / SEC 1 and for the quantum
  part Ekerå–Håstad and the resource estimates of Gidney–Ekera.

Positioning of this repository's `shor/` package:

1. the *number-theoretic* core (modular exponentiation, order finding, continued-fraction
   recovery of the period, RSA key recovery from `φ(n)`, and the EC group law) is verified
   with executable `Nat`/`ZMod` functions and `decide`/kernel-checked proofs;
2. the *quantum* core (modular-exponentiation oracle circuits, QFT, inverse QFT) is expressed
   in the same deeply embedded `Circuit` language as the optimiser, with matrix semantics,
   so the verified optimisation passes apply to it;
3. the classical/quantum boundary is stated explicitly: what is proved is that the *circuit*
   implements the intended permutation and that the classical post-processing recovers the
   secret whenever the measured order/period is the true one. Sampling probability bounds
   (how often the run succeeds) are stated as the remaining gap when they are not proved.
