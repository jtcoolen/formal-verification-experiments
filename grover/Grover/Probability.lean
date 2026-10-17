/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 3 (consequence): the exact success probability

`pSuccess θ k` is, by definition, the Born-rule probability of measuring the marked state in
the state produced by `k` Grover iterations in the reduced model.  The theorem
`pSuccess_eq` identifies it with the closed form

```
P_success(k) = sin² ((2k + 1) θ),      θ = arcsin (1 / √N).
```

No approximation is involved: this is an exact identity over `ℝ`.
-/
import Grover.Amplitude

open Matrix

noncomputable section

namespace Grover

/-- The success probability of the reduced model after `k` Grover iterations: the Born-rule
probability of measuring the marked state. -/
def pSuccess (θ : ℝ) (k : ℕ) : ℝ := probMarked (iterate θ k)

/-- `pSuccess` really is the squared marked amplitude of the iterated state. -/
theorem pSuccess_def (θ : ℝ) (k : ℕ) : pSuccess θ k = (iterate θ k 0) ^ 2 := rfl

/-- **Exact success probability of Grover's algorithm** (reduced model). -/
theorem pSuccess_eq (θ : ℝ) (k : ℕ) :
    pSuccess θ k = Real.sin (((2 : ℝ) * k + 1) * θ) ^ 2 := by
  rw [pSuccess, iterate_eq_state, probMarked]
  simp

theorem pSuccess_nonneg (θ : ℝ) (k : ℕ) : 0 ≤ pSuccess θ k := by
  rw [pSuccess_eq]
  exact pow_two_nonneg _

theorem pSuccess_le_one (θ : ℝ) (k : ℕ) : pSuccess θ k ≤ 1 := by
  rw [pSuccess_eq]
  have h := Real.sin_sq_add_cos_sq (((2 : ℝ) * k + 1) * θ)
  nlinarith [pow_two_nonneg (Real.cos (((2 : ℝ) * k + 1) * θ))]

/-- The failure probability of the reduced model. -/
def pFailure (θ : ℝ) (k : ℕ) : ℝ := (iterate θ k 1) ^ 2

theorem pFailure_eq (θ : ℝ) (k : ℕ) :
    pFailure θ k = Real.cos (((2 : ℝ) * k + 1) * θ) ^ 2 := by
  rw [pFailure, iterate_eq_state]
  simp

theorem pSuccess_add_pFailure (θ : ℝ) (k : ℕ) : pSuccess θ k + pFailure θ k = 1 := by
  rw [pSuccess_eq, pFailure_eq]
  exact Real.sin_sq_add_cos_sq (((2 : ℝ) * k + 1) * θ)

end Grover
