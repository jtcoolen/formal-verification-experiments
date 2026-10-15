/-
Small-scale matrix arithmetic helpers used by the gate libraries:
exact formulas for the entries of a product of 2x2 and 4x4 complex matrices,
the unitarity predicate used throughout the project, and the exact phase identities
exp(i*pi) = -1 and exp(i*pi/2) = i.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential

namespace Quantum

/-- A square complex matrix is unitary when multiplying by its conjugate transpose gives the
identity in both orders. -/
def IsUnitaryM {α : Type _} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) : Prop :=
  M * M.conjTranspose = 1 ∧ M.conjTranspose * M = 1

theorem isUnitaryM_one {α : Type _} [Fintype α] [DecidableEq α] : IsUnitaryM (1 : Matrix α α ℂ) :=
  ⟨by rw [Matrix.conjTranspose_one, Matrix.one_mul],
   by rw [Matrix.conjTranspose_one, Matrix.mul_one]⟩

theorem isUnitaryM_mul {α : Type _} [Fintype α] [DecidableEq α]
    {M N : Matrix α α ℂ} (hM : IsUnitaryM M) (hN : IsUnitaryM N) : IsUnitaryM (M * N) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      (Matrix.mul_assoc N N.conjTranspose M.conjTranspose).symm, hN.1, Matrix.one_mul, hM.1]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      (Matrix.mul_assoc M.conjTranspose M N).symm, hM.2, Matrix.one_mul, hN.2]

lemma sum_bool_eq (f : Bool → ℂ) : (∑ b : Bool, f b) = f false + f true := by
  classical
  have h : (Finset.univ : Finset Bool) = insert false ({true} : Finset Bool) := by decide
  calc (∑ b : Bool, f b) = ∑ b ∈ (Finset.univ : Finset Bool), f b := rfl
    _ = f false + f true := by rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

lemma sum_prod_bool_eq (f : Bool × Bool → ℂ) :
    (∑ k : Bool × Bool, f k) =
      f (false, false) + f (false, true) + f (true, false) + f (true, true) := by
  classical
  have h : (Finset.univ : Finset (Bool × Bool)) =
      insert (false, false) (insert (false, true) (insert (true, false)
        {(true, true)} : Finset (Bool × Bool))) := by decide
  calc (∑ k : Bool × Bool, f k) = ∑ k ∈ (Finset.univ : Finset (Bool × Bool)), f k := rfl
    _ = f (false, false) + f (false, true) + f (true, false) + f (true, true) := by
      rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      abel

/-- Entrywise multiplication of two 2x2 complex matrices. -/
lemma mul2_apply (M N : Matrix Bool Bool ℂ) (i j : Bool) :
    (M * N) i j = M i false * N false j + M i true * N true j := by
  rw [Matrix.mul_apply, sum_bool_eq]

/-- Entrywise multiplication of two 4x4 complex matrices. -/
lemma mul4_apply (M N : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Bool × Bool) :
    (M * N) i j =
      M i (false, false) * N (false, false) j + M i (false, true) * N (false, true) j +
        M i (true, false) * N (true, false) j + M i (true, true) * N (true, true) j := by
  rw [Matrix.mul_apply, sum_prod_bool_eq]

lemma conjTranspose_entry (M : Matrix Bool Bool ℂ) (i j : Bool) :
    M.conjTranspose i j = star (M j i) := rfl

lemma conjTranspose_entry4 (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Bool × Bool) :
    M.conjTranspose i j = star (M j i) := rfl

theorem exp_pi_I : Complex.exp (Real.pi * Complex.I) = -1 := by
  apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Real.cos_pi, Real.sin_pi]

theorem exp_neg_pi_I : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
  rw [Complex.exp_neg, exp_pi_I]
  norm_num

theorem exp_half_pi_I : Complex.exp (Complex.I * (Real.pi / 2)) = Complex.I := by
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem exp_neg_half_pi_I : Complex.exp (-(Complex.I * (Real.pi / 2))) = -Complex.I := by
  rw [Complex.exp_neg, exp_half_pi_I]
  field_simp
  norm_num

/-- Conjugation of a pure phase. -/
lemma star_exp_I (x : ℝ) :
    star (Complex.exp (Complex.I * x)) = Complex.exp (-(Complex.I * x)) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I]
  rw [show (starRingEnd ℂ) (x : ℂ) = (x : ℂ) by
    simp [Complex.star_def, Complex.conj_ofReal]]
  ring

end Quantum