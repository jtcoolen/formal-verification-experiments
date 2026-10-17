/-
# Grover

Machine-checked formalization of Grover's quantum search algorithm: the exact success
probability after `k` iterations, the recommended iteration count, and an `O(√N)`
oracle-query upper bound.  Importing this module gives the whole development.

* `Grover.States` — Phase 1: the reduced two-dimensional state space, normalization,
  Born-rule measurement probability.
* `Grover.Rotation` — planar rotations as matrices; `rot a *ᵥ state φ = state (φ + a)`.
* `Grover.Oracle` — Phase 2: the phase oracle `diag (-1, 1)`.
* `Grover.Diffusion` — Phase 2: the diffusion operator `2|s⟩⟨s| - I` and the proof that
  `D * O = rot (2θ)`.
* `Grover.Amplitude` — Phase 3: `G ^ k *ᵥ state θ = state ((2k+1) θ)`.
* `Grover.Probability` — Phase 3: `pSuccess θ k = sin² ((2k+1) θ)`.
* `Grover.Complexity` — Phase 4: `k_opt = ⌊π/(4θ)⌋`, `pSuccess ≥ 1 - 1/N`, `k_opt ≤ (π/4)√N`.
* `Grover.FullSpace` — Phase 5: the genuine `N`-dimensional complex Hilbert space, oracle and
  diffusion operators, and the transfer of the probability and query bounds.
* `Grover.Examples` — Phase 6: the instances N = 2, 4, 8, 16 and an executable simulator.
-/
import Grover.Basic
import Grover.States
import Grover.Rotation
import Grover.Oracle
import Grover.Diffusion
import Grover.Amplitude
import Grover.Probability
import Grover.Complexity
import Grover.FullSpace
