/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Executable numerical simulator (demonstration only)

This module is *not* part of the verified mathematical core.  It is a `Float` evaluator for the
two-dimensional rotation that `Grover.Amplitude` proves to be the Grover iteration, provided so
that a reader can watch the amplitudes move.  No theorem of this repository depends on it, and
floating-point output is never used as evidence for a proof: the exact statements live in
`Grover.Probability` and `Grover.FullSpace`.
-/

namespace Grover.Simulator

/-- `θ` as a machine number: `asin (1/√N)`. -/
def thetaF (N : Nat) : Float :=
  Float.asin (1 / Float.sqrt (Nat.toFloat N))

/-- One Grover iteration on the pair of amplitudes `(marked, unmarked)`, using
`sin 2θ = 2 sin θ cos θ` and `cos 2θ = 1 - 2 sin² θ`. -/
def groverStep (s c : Float) (a b : Float) : Float × Float :=
  let s2 := 2 * s * c
  let c2 := 1 - 2 * s * s
  (c2 * a + s2 * b, -s2 * a + c2 * b)

/-- Iterate the two-dimensional Grover rotation `k` times and return the squared marked
amplitude, i.e. the success probability. -/
def simulate (N k : Nat) : Float :=
  let s : Float = 1 / Float.sqrt (Nat.toFloat N)
  let c : Float := Float.sqrt (1 - s * s)
  go s c k s c
  where
    go (s c : Float) : Nat → Float → Float → Float
      | 0, a, b => a * a
      | k + 1, a, b =>
          let (a', b') := groverStep s c a b
          go s c k a' b'

/-- The simulator's own guess at the recommended iteration count: `⌊π / (4θ)⌋`, computed in
machine arithmetic.  The verified definition is `Grover.kOpt`. -/
def kApprox (N : Nat) : Nat :=
  Float.toNat (Float.pi / (4 * thetaF N))

/-- Run the recommended schedule and report the simulated success probability. -/
def simulateOptimal (N : Nat) : Nat × Float := (kApprox N, simulate N (kApprox N))

end Grover.Simulator
