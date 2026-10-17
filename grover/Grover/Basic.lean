/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Grover: basic conventions

This module fixes the conventions shared by every file of the formalization:

* the *reduced* two-dimensional model lives in `Grover.State` (= `Fin 2 → ℝ`), where
  coordinate `0` is the amplitude of the marked basis state and coordinate `1` is the
  amplitude of the normalized superposition of all unmarked basis states;
* the *physical* model (Phase 5) lives in `Grover.HilbertSpace N`
  (= `EuclideanSpace ℂ (Fin N)`), Mathlib's finite-dimensional complex Hilbert space;
* `θ` always denotes `Real.arcsin (1 / Real.sqrt N)`, the Grover half-angle, and one Grover
  iteration costs exactly one invocation of the phase oracle.

All trigonometric quantities are real; complex amplitudes only appear in the full-space
development, where the amplitudes that matter happen to be real anyway.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup

noncomputable section

namespace Grover

/-- The search-space size as a real number, with the standing hypothesis `2 ≤ N`. -/
theorem N_ge_two {N : ℕ} (hN : 2 ≤ N) : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN

/-- `θ N = Real.arcsin (1 / Real.sqrt N)` is the Grover half-angle: the angle whose sine is
the initial amplitude `1/√N` of the marked state in the uniform superposition. -/
def theta (N : ℝ) : ℝ := Real.arcsin (1 / Real.sqrt N)

/-- The number of Grover iterations that (nearly) maximizes the success probability:
`k_opt N = ⌊π / (4 * θ N)⌋`.  One iteration = one oracle call. -/
def kOpt (N : ℝ) : ℕ := Nat.floor (Real.pi / (4 * theta N))

end Grover
