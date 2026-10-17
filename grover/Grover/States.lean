/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 1: the reduced two-dimensional state space

A state of the reduced model is a pair of real amplitudes

```
coordinate 0 = amplitude of the marked basis state |w⟩
coordinate 1 = amplitude of |r⟩, the normalized superposition of all unmarked basis states
```

This file provides the inner product, the squared norm, the normalization predicate, the
Born-rule probability of observing the marked state, and the one-parameter family
`state φ = (sin φ, cos φ)` of normalized states.  Everything here is plain linear algebra on
`Fin 2 → ℝ`; the connection with the physical `N`-dimensional model is *proved*, not assumed,
in `Grover/FullSpace.lean`, and `normSq_eq_norm_sq_toLp` identifies `normSq` with Mathlib's
Hilbert-space norm on `EuclideanSpace ℝ (Fin 2)`.
-/
import Grover.Basic

open Matrix

noncomputable section

namespace Grover

/-- A state of the reduced two-dimensional model: `x 0` is the amplitude of the marked state
and `x 1` the amplitude of the normalized superposition of the unmarked states. -/
abbrev State := Fin 2 → ℝ

/-- The Euclidean inner product on `State`. -/
def inner2 (x y : State) : ℝ := ∑ i : Fin 2, x i * y i

/-- The squared Euclidean norm of a state. -/
def normSq (x : State) : ℝ := inner2 x x

/-- A state is normalized when its squared norm is `1`, i.e. the total measurement
probability is `1`. -/
def Normalized (x : State) : Prop := normSq x = 1

/-- The Born-rule probability of measuring the marked state: the squared modulus of the
marked amplitude.  For a normalized state this is a probability in `(0, 1)`. -/
def probMarked (x : State) : ℝ := x 0 ^ 2

/-- The normalized state whose marked amplitude is `sin φ` and whose unmarked amplitude is
`cos φ`. -/
def state (φ : ℝ) : State := ![Real.sin φ, Real.cos φ]

@[simp] theorem state_zero (φ : ℝ) : state φ 0 = Real.sin φ := by simp [state]
@[simp] theorem state_one (φ : ℝ) : state φ 1 = Real.cos φ := by simp [state]

section InnerProduct

variable (x y z : State) (c : ℝ)

theorem inner2_apply : inner2 x y = x 0 * y 0 + x 1 * y 1 := by
  simp only [inner2, Fin.sum_univ_two]

theorem normSq_apply : normSq x = x 0 ^ 2 + x 1 ^ 2 := by
  rw [normSq, inner2_apply]
  ring

theorem inner2_comm : inner2 x y = inner2 y x := by
  rw [inner2_apply, inner2_apply]
  ring

theorem inner2_add_left : inner2 (x + y) z = inner2 x z + inner2 y z := by
  simp only [inner2_apply, Pi.add_apply]
  ring

theorem inner2_add_right : inner2 x (y + z) = inner2 x y + inner2 x z := by
  simp only [inner2_apply, Pi.add_apply]
  ring

theorem inner2_smul_left : inner2 (c • x) y = c * inner2 x y := by
  simp only [inner2_apply, Pi.smul_apply]
  ring

theorem inner2_smul_right : inner2 x (c • y) = c * inner2 x y := by
  simp only [inner2_apply, Pi.smul_apply]
  ring

theorem normSq_nonneg : 0 ≤ normSq x := by
  rw [normSq_apply]
  exact add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)

theorem normSq_eq_zero : normSq x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h0 : x 0 ^ 2 = 0 := by
      have h1 : 0 ≤ x 1 ^ 2 := pow_two_nonneg _
      nlinarith [normSq_apply x, h]
    have h1 : x 1 ^ 2 = 0 := by
      have h0' : 0 ≤ x 0 ^ 2 := pow_two_nonneg _
      nlinarith [normSq_apply x, h]
    have hx0 : x 0 = 0 := by nlinarith
    have hx1 : x 1 = 0 := by nlinarith
    ext i
    fin_cases i <;> assumption
  · intro h
    rw [h, normSq_apply]
    simp

theorem normSq_add : normSq (x + y) = normSq x + 2 * inner2 x y + normSq y := by
  rw [normSq_apply, normSq_apply, normSq_apply, inner2_apply]
  simp only [Pi.add_apply]
  ring

theorem normSq_smul : normSq (c • x) = c ^ 2 * normSq x := by
  rw [normSq_apply, normSq_apply]
  simp only [Pi.smul_apply]
  ring

end InnerProduct

section TheStateFamily

variable (φ : ℝ)

theorem normSq_state : normSq (state φ) = 1 := by
  rw [normSq_apply]
  simp only [state_zero, state_one]
  exact Real.sin_sq_add_cos_sq φ

theorem Normalized.state : Normalized (state φ) := normSq_state φ

theorem probMarked_state : probMarked (state φ) = Real.sin φ ^ 2 := by
  simp [probMarked]

theorem probMarked_complement : state φ 1 ^ 2 = 1 - probMarked (state φ) := by
  simp only [probMarked, state_one, state_zero]
  nlinarith [Real.sin_sq_add_cos_sq φ]

end TheStateFamily

section Measurement

variable (x : State)

/-- For a normalized state the marked probability is at most `1`. -/
theorem probMarked_le_one (h : Normalized x) : probMarked x ≤ 1 := by
  have hsum : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    rw [← normSq_apply]
    exact h
  have h1 : 0 ≤ x 1 ^ 2 := pow_two_nonneg _
  simp only [probMarked]
  nlinarith

/-- For a normalized state the marked probability is non-negative, so it really is a
probability. -/
theorem probMarked_nonneg : 0 ≤ probMarked x := by
  simp only [probMarked]
  exact pow_two_nonneg _

/-- The two measurement probabilities of a normalized state sum to `1`. -/
theorem probMarked_add_probUnmarked (h : Normalized x) : probMarked x + x 1 ^ 2 = 1 := by
  have hsum : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    rw [← normSq_apply]
    exact h
  simp only [probMarked]
  nlinarith

end Measurement

/-- The reduced squared norm agrees with Mathlib's Hilbert-space norm on
`EuclideanSpace ℝ (Fin 2)`: `normSq` is the ordinary Euclidean norm, not an ad-hoc quantity. -/
theorem normSq_eq_norm_sq_toLp (x : State) : normSq x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, normSq_apply, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Entrywise computation of a `2 × 2` matrix-vector product.  Use together with the `rfl`
entry lemmas of the concrete matrices of this formalization. -/
theorem mulVec_fin_two {α : Type*} [NonUnitalNonAssocSemiring α]
    (A : Matrix (Fin 2) (Fin 2) α) (x : Fin 2 → α) :
    A *ᵥ x = ![A 0 0 * x 0 + A 0 1 * x 1, A 1 0 * x 0 + A 1 1 * x 1] := by
  ext i
  fin_cases i
  · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
    simp
  · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
    simp

/-- Entrywise computation of the product of two `2 × 2` matrices. -/
theorem mul_fin_two {α : Type*} [NonUnitalNonAssocSemiring α]
    (A B : Matrix (Fin 2) (Fin 2) α) :
    A * B = !![A 0 0 * B 0 0 + A 0 1 * B 1 0, A 0 0 * B 0 1 + A 0 1 * B 1 1;
               A 1 0 * B 0 0 + A 1 1 * B 1 0, A 1 0 * B 0 1 + A 1 1 * B 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp

end Grover
