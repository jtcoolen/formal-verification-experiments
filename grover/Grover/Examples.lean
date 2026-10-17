/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 6: concrete instances

The theorems of Phases 1–5 are stated for an arbitrary size `N`.  This file instantiates them
at `N = 2, 4, 8, 16` and proves the exact closed-form values that are usually obtained by
simulation — in particular `P_success(4, 1) = 1`.

Nothing here is used by the general theorems; the numerical simulator lives in
`Grover.Simulator` and is likewise *not* evidence for any theorem.
-/
import Grover.FullSpace

open Real

noncomputable section

namespace Grover.Examples

section SmallAngles

/-- `θ 2 = π / 4`: with two candidates one Grover iteration rotates by a right angle. -/
theorem theta_two : Grover.theta 2 = π / 4 := by
  show arcsin (1 / sqrt 2) = π / 4
  have h : (1 / sqrt 2 : ℝ) = sin (π / 4) := by
    rw [sin_pi_div_four]
    have h₂ : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
    field_simp [h₂.ne']
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [h, arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

/-- `θ 4 = π / 6`. -/
theorem theta_four : Grover.theta 4 = π / 6 := by
  show arcsin (1 / sqrt 4) = π / 6
  have h : (1 / sqrt 4 : ℝ) = 1 / 2 := by
    have : sqrt 4 = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    rw [this]
  rw [h, ← sin_pi_div_six, arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

/-- `θ 8 = arcsin (1 / (2√2))`. -/
theorem theta_eight : Grover.theta 8 = arcsin (1 / (2 * sqrt 2)) := by
  show arcsin (1 / sqrt 8) = arcsin (1 / (2 * sqrt 2))
  congr 1
  have : (sqrt 8 : ℝ) = 2 * sqrt 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [this]

/-- `θ 16 = arcsin (1/4)`. -/
theorem theta_sixteen : Grover.theta 16 = arcsin (1 / 4) := by
  show arcsin (1 / sqrt 16) = arcsin (1 / 4)
  congr 1
  have : (sqrt 16 : ℝ) = 4 := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    norm_num
  rw [this]

end SmallAngles

section ExactSuccess

/-- **Exact one-iteration success for `N = 4`.**  Grover's original example: with four
candidates a single iteration finds the marked item with probability exactly `1`. -/
theorem pSuccess_four_one : Grover.pSuccess (Grover.theta 4) 1 = 1 := by
  rw [Grover.pSuccess_eq, theta_four]
  have h : ((2 : ℝ) * (1 : ℕ) + 1) * (π / 6) = π / 2 := by ring
  rw [h, Real.sin_pi_div_two]
  norm_num

/-- The same statement in the physical model: measuring one of four items after a single
Grover iteration succeeds with probability `1`. -/
theorem probMeasure_four_one (w : Fin 4) : Grover.probMeasure w (Grover.iterateFull w 1) = 1 := by
  rw [Grover.probMeasure_eq_pSuccess (by norm_num : (2 : ℝ) ≤ (4 : ℕ)) w 1]
  exact pSuccess_four_one

/-- `N = 2`: one iteration gives probability exactly `1/2`. -/
theorem pSuccess_two_one : Grover.pSuccess (Grover.theta 2) 1 = 1 / 2 := by
  rw [Grover.pSuccess_eq, theta_two]
  have h : ((2 : ℝ) * (1 : ℕ) + 1) * (π / 4) = 3 * π / 4 := by ring
  rw [h]
  have h₁ : Real.sin (3 * π / 4) = Real.sin (π / 4) := by
    have : (3 : ℝ) * π / 4 = π - π / 4 := by ring
    rw [this, Real.sin_pi_sub]
  rw [h₁, sin_pi_div_four]
  have h₂ : (sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, sq, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  rw [h₂]

/-- Zero iterations always returns the initial probability `1/N`. -/
theorem pSuccess_zero (N : ℝ) (hN : 1 ≤ N) : Grover.pSuccess (Grover.theta N) 0 = 1 / N := by
  rw [Grover.pSuccess_eq]
  have h : ((2 : ℝ) * (0 : ℕ) + 1) * Grover.theta N = Grover.theta N := by ring
  rw [h, Grover.sin_theta N hN, div_pow, one_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ N)]

end ExactSuccess

section Instances

/-- `N = 2`: `k_opt` queries succeed with probability ≥ `1/2`. -/
theorem success_two : 1 - 1 / (2 : ℝ) ≤ Grover.pSuccess (Grover.theta 2) (Grover.kOpt 2) :=
  Grover.pSuccess_kOpt 2 (by norm_num)

/-- `N = 4`: `k_opt` queries succeed with probability ≥ `3/4`. -/
theorem success_four : 1 - 1 / (4 : ℝ) ≤ Grover.pSuccess (Grover.theta 4) (Grover.kOpt 4) :=
  Grover.pSuccess_kOpt 4 (by norm_num)

/-- `N = 8`. -/
theorem success_eight : 1 - 1 / (8 : ℝ) ≤ Grover.pSuccess (Grover.theta 8) (Grover.kOpt 8) :=
  Grover.pSuccess_kOpt 8 (by norm_num)

/-- `N = 16`. -/
theorem success_sixteen : 1 - 1 / (16 : ℝ) ≤ Grover.pSuccess (Grover.theta 16) (Grover.kOpt 16) :=
  Grover.pSuccess_kOpt 16 (by norm_num)

/-- The query bounds at the four example sizes. -/
theorem queries_two : (Grover.kOpt 2 : ℝ) ≤ π / 4 * sqrt 2 := Grover.kOpt_le_sqrt 2 (by norm_num)
theorem queries_four : (Grover.kOpt 4 : ℝ) ≤ π / 4 * sqrt 4 := Grover.kOpt_le_sqrt 4 (by norm_num)
theorem queries_eight : (Grover.kOpt 8 : ℝ) ≤ π / 4 * sqrt 8 := Grover.kOpt_le_sqrt 8 (by norm_num)
theorem queries_sixteen : (Grover.kOpt 16 : ℝ) ≤ π / 4 * sqrt 16 :=
  Grover.kOpt_le_sqrt 16 (by norm_num)

/-- The physical (full-space) versions, for every marked element of every example size. -/
theorem full_success_two (w : Fin 2) :
    1 - 1 / (2 : ℝ) ≤ Grover.probMeasure w (Grover.iterateFull w (Grover.kOpt 2)) :=
  Grover.grover_success_kOpt (by norm_num) w

theorem full_success_four (w : Fin 4) :
    1 - 1 / (4 : ℝ) ≤ Grover.probMeasure w (Grover.iterateFull w (Grover.kOpt 4)) :=
  Grover.grover_success_kOpt (by norm_num) w

theorem full_success_eight (w : Fin 8) :
    1 - 1 / (8 : ℝ) ≤ Grover.probMeasure w (Grover.iterateFull w (Grover.kOpt 8)) :=
  Grover.grover_success_kOpt (by norm_num) w

theorem full_success_sixteen (w : Fin 16) :
    1 - 1 / (16 : ℝ) ≤ Grover.probMeasure w (Grover.iterateFull w (Grover.kOpt 16)) :=
  Grover.grover_success_kOpt (by norm_num) w

end Instances

end Grover.Examples
