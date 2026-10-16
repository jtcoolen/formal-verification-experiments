/-
Parameterized rotation gate matrices, in exact complex arithmetic.

Rz(theta) = diag(exp(-i theta/2), exp(i theta/2)), Rx(theta) = cos(theta/2) I - i sin(theta/2) X,
Ry(theta) = cos(theta/2) I - i sin(theta/2) Y, and CRz(theta) the controlled version of Rz.
Angles are exact (Quantum.Angle): a rational number of radians plus a rational multiple of pi.
-/
import Quantum.MatrixCalc
import Quantum.Angle
import Quantum.Gates
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Quantum

open Complex Real

noncomputable section

def Rz2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then Complex.exp (Complex.I * (if x then t / 2 else -(t / 2))) else 0

/-- Rx(theta) = cos(theta/2) I - i sin(theta/2) X, exactly. -/

def Rx2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else -Complex.I * (Real.sin (t / 2) : ℂ)

/-- Ry(theta) = cos(theta/2) I - i sin(theta/2) Y, exactly. -/

def Ry2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else if x then (Real.sin (t / 2) : ℂ)
    else -(Real.sin (t / 2) : ℂ)

/-! ### Two-qubit gate matrices -/

/-- Controlled-Rz: the control is the first component, the target the second. -/

def CRz4 (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x = y then if x.1 then
      Complex.exp (Complex.I * (if x.2 then t / 2 else -(t / 2))) else 1 else 0

end

/-! ### Entrywise descriptions of the rotation matrices -/

@[simp] lemma Rz2_false_false (t : ℝ) :
    Rz2 t false false = Complex.exp (-(Complex.I * (t / 2))) := by simp [Rz2]
@[simp] lemma Rz2_true_true (t : ℝ) :
    Rz2 t true true = Complex.exp (Complex.I * (t / 2)) := by simp [Rz2]
@[simp] lemma Rz2_true_false (t : ℝ) : Rz2 t true false = 0 := by simp [Rz2]
@[simp] lemma Rz2_false_true (t : ℝ) : Rz2 t false true = 0 := by simp [Rz2]

@[simp] lemma Rx2_false_false (t : ℝ) : Rx2 t false false = (Real.cos (t / 2) : ℂ) := by
  simp [Rx2]
@[simp] lemma Rx2_true_true (t : ℝ) : Rx2 t true true = (Real.cos (t / 2) : ℂ) := by
  simp [Rx2]
@[simp] lemma Rx2_true_false (t : ℝ) :
    Rx2 t true false = -Complex.I * (Real.sin (t / 2) : ℂ) := by simp [Rx2]
@[simp] lemma Rx2_false_true (t : ℝ) :
    Rx2 t false true = -Complex.I * (Real.sin (t / 2) : ℂ) := by simp [Rx2]

@[simp] lemma Ry2_false_false (t : ℝ) : Ry2 t false false = (Real.cos (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_true_true (t : ℝ) : Ry2 t true true = (Real.cos (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_true_false (t : ℝ) : Ry2 t true false = (Real.sin (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_false_true (t : ℝ) : Ry2 t false true = -(Real.sin (t / 2) : ℂ) := by
  simp [Ry2]

/-! ### Elementary identities about the phases -/

lemma half_add (s t : ℝ) : ((s + t : ℝ) / 2) = s / 2 + t / 2 := by ring

lemma half_add_complex (s t : ℝ) : ((s + t : ℂ) / 2) = s / 2 + t / 2 := by ring

lemma exp_I_add (s t : ℝ) :
    Complex.exp (Complex.I * (s / 2)) * Complex.exp (Complex.I * (t / 2)) =
      Complex.exp (Complex.I * ((s + t) / 2)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma exp_neg_I_add (s t : ℝ) :
    Complex.exp (-(Complex.I * (s / 2))) * Complex.exp (-(Complex.I * (t / 2))) =
      Complex.exp (-(Complex.I * ((s + t) / 2))) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma neg_I_mul_neg_I (x y : ℂ) : (-Complex.I * x) * (-Complex.I * y) = -(x * y) := by
  calc (-Complex.I * x) * (-Complex.I * y) = (Complex.I * Complex.I) * (x * y) := by ring
    _ = (-1 : ℂ) * (x * y) := by rw [Complex.I_mul_I]
    _ = -(x * y) := by ring

/-- Conjugation commutes with the complex exponential. -/
lemma star_exp (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  rw [Complex.star_def, ← Complex.exp_conj]

lemma star_complex_ofReal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  simp [Complex.star_def]

lemma star_complex_I : star Complex.I = -Complex.I := by simp [Complex.star_def]

lemma exp_I_pi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
  rw [show Complex.I * (Real.pi : ℂ) = Real.pi * Complex.I by ring, exp_pi_I]

lemma exp_neg_I_pi : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
  rw [show -(Complex.I * (Real.pi : ℂ)) = -(Real.pi * Complex.I) by ring, exp_neg_pi_I]

lemma exp_I_pi_div_two : Complex.exp (Complex.I * (Real.pi / 2 : ℝ)) = Complex.I := by
  convert exp_half_pi_I using 1 <;> push_cast <;> ring

lemma exp_neg_I_pi_div_two :
    Complex.exp (-(Complex.I * (Real.pi / 2 : ℝ))) = -Complex.I := by
  convert exp_neg_half_pi_I using 1 <;> push_cast <;> ring

lemma two_pi_div_two : ((2 * Real.pi : ℝ) / 2) = Real.pi := by ring

/-! ### Elementary identities -/

theorem Rz2_mul (s t : ℝ) : Rz2 s * Rz2 t = Rz2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul2_apply, exp_I_add, exp_neg_I_add, half_add_complex]

theorem Rz2_zero : Rz2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pi.one_apply]

/-- Rz(2 pi) is *not* the identity: it is the identity times the global phase -1. -/

theorem Rz2_twoPi : Rz2 (2 * Real.pi) = (-1 : ℂ) • 1 := by
  have h1 : Complex.I * ((2 * Real.pi : ℝ) / 2) = Complex.I * (Real.pi : ℂ) := by
    push_cast
    ring
  have h2 : -(Complex.I * ((2 * Real.pi : ℝ) / 2)) = -(Complex.I * (Real.pi : ℂ)) := by
    rw [h1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Rz2_false_false, Rz2_true_true, Rz2_true_false, Rz2_false_true, h1, h2,
      exp_I_pi, exp_neg_I_pi, Pi.one_apply, Pi.smul_apply, neg_mul, mul_one, mul_zero,
      zero_mul, neg_zero]

theorem Rx2_mul (s t : ℝ) : Rx2 s * Rx2 t = Rx2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul2_apply, Rx2_false_false, Rx2_true_true, Rx2_true_false, Rx2_false_true,
      neg_I_mul_neg_I, half_add, Real.cos_add, Real.sin_add] <;>
    push_cast <;> ring

theorem Rx2_zero : Rx2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx2, Pi.one_apply, Real.cos_zero, Real.sin_zero]

theorem Ry2_mul (s t : ℝ) : Ry2 s * Ry2 t = Ry2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul2_apply, Ry2_false_false, Ry2_true_true, Ry2_true_false, Ry2_false_true,
      half_add, Real.cos_add, Real.sin_add] <;>
    push_cast <;> ring

theorem Ry2_zero : Ry2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry2, Pi.one_apply, Real.cos_zero, Real.sin_zero]

/-- Rz(pi) equals the Pauli Z gate up to the global phase -i. -/
theorem Rz2_pi_Z2 : Rz2 Real.pi = (-Complex.I) • Z2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz2, Z2, Pi.smul_apply, two_pi_div_two, exp_I_pi_div_two, exp_neg_I_pi_div_two]

/-! ### Two-qubit identities -/

theorem CRz4_mul (s t : ℝ) : CRz4 s * CRz4 t = CRz4 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul4_apply, CRz4, exp_I_add, exp_neg_I_add, half_add_complex]

theorem CRz4_zero : CRz4 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CRz4, Pi.one_apply]

/-! ### Adjointness and unitarity of the primitives -/

theorem Rz2_conjTranspose (t : ℝ) : (Rz2 t).conjTranspose = Rz2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz2, conjTranspose_entry, star_exp, Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, neg_div]

theorem Rx2_conjTranspose (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx2, conjTranspose_entry, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
      neg_div]

theorem Ry2_conjTranspose (t : ℝ) : (Ry2 t).conjTranspose = Ry2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry2, conjTranspose_entry, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
      neg_div]

theorem isUnitary_Rz2 (t : ℝ) : IsUnitaryM (Rz2 t) := by
  rw [Rz2_conjTranspose]
  refine ⟨?_, ?_⟩
  · rw [Rz2_mul, neg_add_self, Rz2_zero]
  · rw [Rz2_mul, add_right_neg, Rz2_zero]

theorem isUnitary_Rx2 (t : ℝ) : IsUnitaryM (Rx2 t) := by
  rw [Rx2_conjTranspose]
  refine ⟨?_, ?_⟩
  · rw [Rx2_mul, neg_add_self, Rx2_zero]
  · rw [Rx2_mul, add_right_neg, Rx2_zero]

theorem isUnitary_Ry2 (t : ℝ) : IsUnitaryM (Ry2 t) := by
  rw [Ry2_conjTranspose]
  refine ⟨?_, ?_⟩
  · rw [Ry2_mul, neg_add_self, Ry2_zero]
  · rw [Ry2_mul, add_right_neg, Ry2_zero]

theorem CRz4_conjTranspose (t : ℝ) : (CRz4 t).conjTranspose = CRz4 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CRz4, conjTranspose_entry4, star_exp, Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, neg_div, Prod.mk.injEq]

theorem isUnitary_CRz4 (t : ℝ) : IsUnitaryM (CRz4 t) := by
  rw [CRz4_conjTranspose]
  refine ⟨?_, ?_⟩
  · rw [CRz4_mul, neg_add_self, CRz4_zero]
  · rw [CRz4_mul, add_right_neg, CRz4_zero]

/-! ### The requested identity Rz2 Real.pi = (-Complex.I) • S2 is false -/

theorem Rz2_pi_phase_not : ¬ (Rz2 Real.pi = (-Complex.I) • S2) := by
  intro h
  have h1 : (Rz2 Real.pi) true true = Complex.I := by
    rw [Rz2_true_true]
    convert exp_I_pi_div_two using 1 <;> ring
  have h2 : ((-Complex.I) • S2) true true = (1 : ℂ) := by
    simp [S2, Pi.smul_apply]
  have h3 := congrArg (fun M : Matrix Bool Bool ℂ => M true true) h
  rw [h1, h2] at h3
  exact absurd h3 (by norm_num : ¬ (Complex.I : ℂ) = 1)

end Quantum
