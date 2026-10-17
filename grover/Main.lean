/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Demonstration executable

`lake exe grover` prints the verified facts that this repository establishes, instantiated at
concrete search-space sizes, and then runs the (unverified, demonstration-only) floating-point
simulator next to them so the reader can see the two agree.
-/
import Grover
import Grover.Examples
import Grover.Simulator

open Grover Real

noncomputable section

def main : IO Unit := do
  IO.println "=== Grover's algorithm in Lean 4: machine-checked results ==="
  IO.println ""
  IO.println "Exact amplitude law (Grover/Amplitude.lean, Grover/Probability.lean):"
  IO.println "  G^k *ᵥ state θ = state ((2k+1) θ),  P_success(θ,k) = sin²((2k+1) θ)"
  IO.println ""
  IO.println "Closed-form Grover angles proved in Grover/Examples.lean:"
  IO.println s!"  θ 2  = π/4 :  {Examples.theta_two}"
  IO.println s!"  θ 4  = π/6 :  {Examples.theta_four}"
  IO.println s!"  θ 16 = arcsin(1/4)"
  IO.println ""
  IO.println "Exact one-shot success for N = 4 (P_success(θ 4, 1) = 1):"
  IO.println s!"  reduced model :  {Examples.pSuccess_four_one}"
  IO.println s!"  N-dim model   :  {by exact Examples.probMeasure_four_one ⟨0, by omega⟩}"
  IO.println ""
  IO.println "Verified bounds  1 - 1/N ≤ P_success(θ N, k_opt N)  and  k_opt N ≤ (π/4)√N:"
  for (n, p, q) : List (Nat × String × String) :=
      [(2, "success_two", "queries_two"), (4, "success_four", "queries_four"),
       (8, "success_eight", "queries_eight"), (16, "success_sixteen", "queries_sixteen")] do
    IO.println s!"  N = {n} : P ≥ 1 - 1/{n} ({p}),  k_opt ≤ {q}"
  IO.println ""
  IO.println "Floating-point simulator (Grover/Simulator.lean) — a demonstration, not a proof:"
  for n : Nat := [2, 4, 8, 16, 100, 1024] do
    let (k, p) := Simulator.simulateOptimal n
    IO.println s!"  N = {n} : k = {k}, simulated P_success = {p}"
  IO.println ""
  IO.println "Run 'lake env lean Axioms.lean' to see the axiom audit of every main theorem."
