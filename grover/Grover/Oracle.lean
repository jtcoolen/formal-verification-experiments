/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 2 (part 1): the phase oracle in the reduced model

With the coordinate convention of `Grover.State` the phase oracle that flips the sign of the
marked amplitude is the diagonal matrix `diag (-1, 1)`.  This file proves it is orthogonal and
preserves normalization.  In `Grover/FullSpace.lean` the genuine `N`-dimensional oracle is
proved to act on the invariant plane by *this* matrix, so the reduced oracle is a theorem, not
a definition of the algorithm.
-/
import Grover.Rotation

open Matrix

noncomputable section

namespace Grover

/-- The phase oracle `O = diag (-1, 1)` of the reduced model: it multiplies the marked
amplitude by `-1` and leaves the unmarked amplitude alone. -/
def phaseOracle : Matrix (Fin 2) (Fin 2) ℝ := !![(-1 : ℝ), 0; 0, 1]

@[simp] theorem phaseOracle_00 : phaseOracle 0 0 = (-1 : ℝ) := rfl
@[simp] theorem phaseOracle_01 : phaseOracle 0 1 = (0 : ℝ) := rfl
@[simp] theorem phaseOracle_10 : phaseOracle 1 0 = (0 : ℝ) := rfl
@[simp] theorem phaseOracle_11 : phaseOracle 1 1 = (1 : ℝ) := rfl

theorem phaseOracle_mulVec (x : State) : phaseOracle *ᵥ x = ![- x 0, x 1] := by
  rw [mulVec_fin_two, phaseOracle_00, phaseOracle_01, phaseOracle_10, phaseOracle_11]
  simp

/-- The oracle preserves the squared norm. -/
theorem normSq_phaseOracle_mulVec (x : State) : normSq (phaseOracle *ᵥ x) = normSq x := by
  rw [phaseOracle_mulVec, normSq_apply, normSq_apply]
  simp only [cons_val_zero, cons_val_one, cons_val_succ]
  ring

/-- The oracle is orthogonal: `Oᵀ * O = 1`. -/
theorem phaseOracle_orthogonal : phaseOracle ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseOracle, mul_apply, transpose_apply, one_apply, Fin.sum_univ_two]

/-- The oracle preserves normalization. -/
theorem Normalized.phaseOracle_mulVec {x : State} (hx : Normalized x) :
    Normalized (phaseOracle *ᵥ x) := by
  have h1 : normSq x = 1 := hx
  exact (normSq_phaseOracle_mulVec x).trans h1

/-- The oracle is an involution: two oracle calls cancel. -/
theorem phaseOracle_mul_phaseOracle : phaseOracle * phaseOracle = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseOracle, mul_apply, one_apply, Fin.sum_univ_two]

theorem phaseOracle_det : phaseOracle.det = -1 := by
  rw [Matrix.det_fin_two]
  have h00 : phaseOracle 0 0 = (-1 : ℝ) := rfl
  have h01 : phaseOracle 0 1 = (0 : ℝ) := rfl
  have h10 : phaseOracle 1 0 = (0 : ℝ) := rfl
  have h11 : phaseOracle 1 1 = (1 : ℝ) := rfl
  rw [h00, h01, h10, h11]
  ring

end Grover
