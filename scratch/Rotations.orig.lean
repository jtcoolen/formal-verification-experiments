/-
Parameterized rotation gate matrices, in exact complex arithmetic.

Rz(theta) = diag(exp(-i theta/2), exp(i theta/2)), Rx(theta) = cos(theta/2) I - i sin(theta/2) X,
Ry(theta) = cos(theta/2) I - i sin(theta/2) Y, and CRz(theta) the controlled version of Rz.
Angles are exact (Quantum.Angle): a rational number of radians plus a rational multiple of pi.
-/
import Quantum.MatrixCalc
import Quantum.Angle
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

/-- Controlled-NOT: the control is the first component, the target the second. -/

def CRz4 (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x = y then if x.1 then
      Complex.exp (Complex.I * (if x.2 then t / 2 else -(t / 2))) else 1 else 0

end

/-! ### Elementary identities -/

theorem Rz2_mul (s t : ℝ) : Rz2 s * Rz2 t = Rz2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul2_apply, Rz2, Pi.one_apply] <;>
    (try { contradiction }) <;>
    (try
      { rw [show ((0 : ℝ) / 2) = 0 by ring, Complex.exp_zero] <;>
        simp [show ((0 : ℝ) / 2) = 0 by ring] <;> ring_nf <;> norm_num }) <;>
    (try { rw [← Complex.exp_add] <;> ring_nf })

theorem Rz2_zero : Rz2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz2, Pi.one_apply, Complex.exp_zero, show ((0 : ℝ) / 2) = 0 by ring]

/-- Rz(2 pi) is *not* the identity: it is the identity times the global phase -1. -/

theorem Rz2_twoPi : Rz2 (2 * Real.pi) = (-1 : ℂ) • 1 := by
  have h : Complex.exp (Complex.I * Real.pi) = -1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using exp_pi_I
  have h' : Complex.exp (-(Complex.I * Real.pi)) = -1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using exp_neg_pi_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Rz2, Pi.one_apply, smul_apply, neg_div] <;>
    (try { ring_nf at * ; simp_all only [h, h'] }) <;>
    (try { norm_num }) <;>
    (try { contradiction })

theorem Rx2_mul (s t : ℝ) : Rx2 s * Rx2 t = Rx2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul2_apply, Rx2, Pi.one_apply]
  all_goals
    rw [show (s + t) / 2 = s / 2 + t / 2 by ring]
    rw [Real.cos_add, Real.sin_add]
    push_cast
    ring_nf
    <;> simp [Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> ring_nf

theorem Rx2_zero : Rx2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx2, Pi.one_apply, Real.cos_zero, Real.sin_zero]

theorem Ry2_mul (s t : ℝ) : Ry2 s * Ry2 t = Ry2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul2_apply, Ry2, Pi.one_apply]
  all_goals
    rw [show (s + t) / 2 = s / 2 + t / 2 by ring]
    rw [Real.cos_add, Real.sin_add]
    push_cast
    ring_nf
    <;> simp [Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> ring_nf

theorem Ry2_zero : Ry2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry2, Pi.one_apply, Real.cos_zero, Real.sin_zero]

/-- Rz(pi) equals the phase gate S up to the global phase -i. -/

theorem Rz2_pi_phase : Rz2 Real.pi = (-Complex.I) • S2 := by
  have h : Complex.exp (Complex.I * (Real.pi / 2)) = Complex.I := by
    apply Complex.ext <;>
      simp [Complex.exp_re, Complex.exp_im, Real.cos_pi_div_two, Real.sin_pi_div_two]
  have h' : Complex.exp (-(Complex.I * (Real.pi / 2))) = -Complex.I := by
    rw [Complex.exp_neg]
    field_simp [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Rz2, S2, smul_apply] <;>
    (try { ring_nf at * ; simp_all only [h, h'] }) <;>
    (try { norm_num }) <;>
    (try { contradiction })

/-! ### Two-qubit identities -/

theorem CRz4_mul (s t : ℝ) : CRz4 s * CRz4 t = CRz4 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul4_apply, CRz4, Pi.one_apply] <;>
    (try { contradiction }) <;>
    (try
      { rw [show ((0 : ℝ) / 2) = 0 by ring, Complex.exp_zero] <;>
        simp [show ((0 : ℝ) / 2) = 0 by ring] <;> ring_nf <;> norm_num }) <;>
    (try { rw [← Complex.exp_add] <;> ring_nf })

/-! ### Adjointness and unitarity of the primitives -/

/-- A square complex matrix is unitary when multiplying by its conjugate transpose gives the
identity in both orders. -/

theorem Rz2_conjTranspose (t : ℝ) : (Rz2 t).conjTranspose = Rz2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Rz2, conjTranspose_entry, star_exp_I] <;>
    ring_nf <;> simp

theorem Rx2_conjTranspose (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Rx2, conjTranspose_entry, star_def, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_neg, neg_neg]
  all_goals
    rw [show ((-t : ℝ) / 2) = -(t / 2) by ring]
    simp [Real.cos_neg, Real.sin_neg, Complex.ext_iff]
    ring_nf
    simp

theorem Ry2_conjTranspose (t : ℝ) : (Ry2 t).conjTranspose = Ry2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Ry2, conjTranspose_entry, star_def, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_neg, neg_neg]
  all_goals
    rw [show ((-t : ℝ) / 2) = -(t / 2) by ring]
    simp [Real.cos_neg, Real.sin_neg, Complex.ext_iff]
    ring_nf
    simp

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
    simp only [CRz4, conjTranspose_entry4, star_exp_I, Prod.mk.injEq] <;>
    ring_nf <;> simp

theorem isUnitary_CRz4 (t : ℝ) : IsUnitaryM (CRz4 t) := by
  rw [CRz4_conjTranspose]
  refine ⟨?_, ?_⟩
  · rw [CRz4_mul, neg_add_self]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CRz4, Pi.one_apply, Complex.exp_zero, show ((0 : ℝ) / 2) = 0 by ring]
  · rw [CRz4_mul, add_right_neg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CRz4, Pi.one_apply, Complex.exp_zero, show ((0 : ℝ) / 2) = 0 by ring]

/-! ### The specified action of each primitive gate on computational basis states -/

end

end Quantum
