/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 3: amplitude amplification

Starting from the uniform state `state θ`, `k` Grover iterations produce

```
G ^ k *ᵥ state θ = state ((2k + 1) * θ)
```

so the marked amplitude after `k` iterations is exactly `sin ((2k+1) θ)`.  This is the exact
amplitude-amplification law of Grover's algorithm (Grover 1996, §"amplitude amplification";
Boyer–Brassard–Høyer–Tapp 1996 for the exact analysis).
-/
import Grover.Diffusion

open Matrix

noncomputable section

namespace Grover

/-- The state of the reduced model after `k` Grover iterations, starting from the uniform
state `state θ`. -/
def iterate (θ : ℝ) (k : ℕ) : State := groverIter θ ^ k *ᵥ state θ

/-- **Amplitude amplification.**  `k` Grover iterations rotate the uniform state from angle
`θ` to angle `(2k+1) θ`. -/
theorem iterate_eq_state (θ : ℝ) (k : ℕ) :
    iterate θ k = state (((2 : ℝ) * k + 1) * θ) := by
  rw [iterate, groverIter_pow, rot_mulVec_state]
  congr 1
  ring

/-- The iterates are normalized: Grover's algorithm never leaves the unit sphere. -/
theorem Normalized.iterate (θ : ℝ) (k : ℕ) : Normalized (iterate θ k) := by
  rw [iterate_eq_state]
  exact Normalized.state _

/-- The squared norm of every iterate is `1`. -/
theorem normSq_iterate (θ : ℝ) (k : ℕ) : normSq (iterate θ k) = 1 := Normalized.iterate θ k

/-- The marked amplitude after `k` iterations. -/
theorem iterate_zero (θ : ℝ) (k : ℕ) :
    iterate θ k 0 = Real.sin (((2 : ℝ) * k + 1) * θ) := by
  rw [iterate_eq_state]
  simp

/-- The unmarked amplitude after `k` iterations. -/
theorem iterate_one (θ : ℝ) (k : ℕ) :
    iterate θ k 1 = Real.cos (((2 : ℝ) * k + 1) * θ) := by
  rw [iterate_eq_state]
  simp

/-- Zero iterations is the identity: the uniform state is recovered. -/
theorem iterate_zero_iterations (θ : ℝ) : iterate θ 0 = state θ := by
  rw [iterate_eq_state]
  congr 1
  ring

end Grover
