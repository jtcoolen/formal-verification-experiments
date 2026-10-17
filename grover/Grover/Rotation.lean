/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 1/3 support: planar rotations as matrices

`rot a` is the linear map of `Grover.State` whose matrix in the fixed basis `(e 0, e 1)` is

```
[ cos a   sin a ]
[ -sin a  cos a ]
```

With the coordinate convention of `Grover.State` this is the rotation that sends `state φ` to
`state (φ + a)`, i.e. it moves the state *towards* the marked axis by `a`.  The sign pattern is
forced by the matrix product `D * O` computed in `Grover/Diffusion.lean`; it is not a free
choice made to make later proofs convenient.
-/
import Grover.States

open Matrix

noncomputable section

namespace Grover

/-- The rotation whose matrix is `![![cos a, sin a], ![-sin a, cos a]]`, so that
`rot a *ᵥ state φ = state (φ + a)`. -/
def rot (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos a, Real.sin a; -Real.sin a, Real.cos a]

variable (a b : ℝ)

@[simp] theorem rot_00 : rot a 0 0 = Real.cos a := rfl
@[simp] theorem rot_01 : rot a 0 1 = Real.sin a := rfl
@[simp] theorem rot_10 : rot a 1 0 = -Real.sin a := rfl
@[simp] theorem rot_11 : rot a 1 1 = Real.cos a := rfl

theorem rot_val : rot a = !![Real.cos a, Real.sin a; -Real.sin a, Real.cos a] := rfl

theorem rot_zero : rot 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot]

theorem rot_mulVec_apply (x : State) :
    rot a *ᵥ x = ![Real.cos a * x 0 + Real.sin a * x 1, -Real.sin a * x 0 + Real.cos a * x 1] := by
  ext i
  fin_cases i <;>
    simp [mulVec, dotProduct, rot, Fin.sum_univ_two, neg_mul, mul_neg, mul_one, mul_zero,
      add_zero, zero_add, zero_mul]

/-- The fundamental trigonometric action of a rotation on the state family: a rotation by `a`
adds `a` to the Grover angle. -/
theorem rot_mulVec_state (φ : ℝ) : rot a *ᵥ state φ = state (φ + a) := by
  rw [rot_mulVec_apply]
  ext i
  fin_cases i <;>
    simp [state, Real.sin_add, Real.cos_add, neg_mul] <;>
      ring

theorem rot_mul_rot : rot a * rot b = rot (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add, neg_mul, mul_neg,
      mul_comm] <;>
      ring

/-- Rotations compose additively when applied to a state. -/
theorem rot_mulVec_rot_mulVec (x : State) : rot a *ᵥ (rot b *ᵥ x) = rot (a + b) *ᵥ x := by
  rw [mulVec_mulVec, rot_mul_rot]

/-- `rot` is an orthogonal matrix: its transpose is its inverse. -/
theorem rot_orthogonal : rot a ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  have h : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, mul_apply, Fin.sum_univ_two, transpose_apply, one_apply, neg_mul, mul_neg]
  · nlinarith [h]
  · nlinarith [h]
  · nlinarith [h]
  · nlinarith [h]

/-- Rotations preserve the squared norm. -/
theorem normSq_rot_mulVec (x : State) : normSq (rot a *ᵥ x) = normSq x := by
  rw [rot_mulVec_apply, normSq_apply, normSq_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  have key : (Real.cos a * x 0 + Real.sin a * x 1) ^ 2
      + (-Real.sin a * x 0 + Real.cos a * x 1) ^ 2
      = (Real.sin a ^ 2 + Real.cos a ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by ring
  rw [key, Real.sin_sq_add_cos_sq, one_mul]

/-- Rotations preserve normalization. -/
theorem Normalized.rot_mulVec {x : State} (hx : Normalized x) : Normalized (rot a *ᵥ x) := by
  have h1 : normSq x = 1 := hx
  exact (normSq_rot_mulVec a x).trans h1

/-- Powers of a rotation are rotations: `(rot a) ^ n = rot (n * a)`. -/
theorem rot_pow (n : ℕ) : rot a ^ n = rot (↑n * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, rot_zero]
  | succ n ih =>
      rw [pow_succ, ih, rot_mul_rot]
      congr 1
      push_cast
      ring

theorem rot_det : (rot a).det = 1 := by
  rw [Matrix.det_fin_two]
  have h00 : (rot a) 0 0 = Real.cos a := rfl
  have h01 : (rot a) 0 1 = Real.sin a := rfl
  have h10 : (rot a) 1 0 = -Real.sin a := rfl
  have h11 : (rot a) 1 1 = Real.cos a := rfl
  rw [h00, h01, h10, h11]
  have h : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  nlinarith [h]

end Grover
