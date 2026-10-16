import Quantum.MatrixCalc
import Quantum.Angle
import Quantum.Gates
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Quantum
open Complex Real
noncomputable section

#check @neg_add_self
#check @add_right_neg
#check @add_left_neg
#check @Complex.I_ne_one
#check @Complex.cos_conj

def Rz2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then Complex.exp (Complex.I * (if x then t / 2 else -(t / 2))) else 0

def Rx2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else -Complex.I * (Real.sin (t / 2) : ℂ)

def Ry2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else if x then (Real.sin (t / 2) : ℂ)
    else -(Real.sin (t / 2) : ℂ)

def CRz4 (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x = y then if x.1 then
      Complex.exp (Complex.I * (if x.2 then t / 2 else -(t / 2))) else 1 else 0

@[simp] lemma Rz2_false_false (t : ℝ) :
    Rz2 t false false = Complex.exp (-(Complex.I * (t / 2))) := by simp [Rz2]
@[simp] lemma Rz2_true_true (t : ℝ) :
    Rz2 t true true = Complex.exp (Complex.I * (t / 2)) := by simp [Rz2]
@[simp] lemma Rz2_true_false (t : ℝ) : Rz2 t true false = 0 := by simp [Rz2]
@[simp] lemma Rz2_false_true (t : ℝ) : Rz2 t false true = 0 := by simp [Rz2]
@[simp] lemma Rx2_false_false (t : ℝ) : Rx2 t false false = (Real.cos (t / 2) : ℂ) := by
  simp [Rx2]
@[simp] lemma Rx2_true_false (t : ℝ) :
    Rx2 t true false = -Complex.I * (Real.sin (t / 2) : ℂ) := by simp [Rx2]
@[simp] lemma Rx2_false_true (t : ℝ) :
    Rx2 t false true = -Complex.I * (Real.sin (t / 2) : ℂ) := by simp [Rx2]
@[simp] lemma Rx2_true_true (t : ℝ) : Rx2 t true true = (Real.cos (t / 2) : ℂ) := by
  simp [Rx2]
@[simp] lemma Ry2_false_false (t : ℝ) : Ry2 t false false = (Real.cos (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_true_false (t : ℝ) : Ry2 t true false = (Real.sin (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_false_true (t : ℝ) : Ry2 t false true = -(Real.sin (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_true_true (t : ℝ) : Ry2 t true true = (Real.cos (t / 2) : ℂ) := by
  simp [Ry2]

lemma star_complex_ofReal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
lemma star_complex_I : star Complex.I = -Complex.I := by simp

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

lemma exp_I_pi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
  rw [show Complex.I * (Real.pi : ℂ) = Real.pi * Complex.I by ring, exp_pi_I]

lemma exp_neg_I_pi : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
  rw [show -(Complex.I * (Real.pi : ℂ)) = -(Real.pi * Complex.I) by ring, exp_neg_pi_I]

theorem Rz2_conjTranspose (t : ℝ) : (Rz2 t).conjTranspose = Rz2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz2, conjTranspose_entry, star_exp]

theorem Rx2_conjTranspose (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [conjTranspose_entry, Rx2_false_false, Rx2_true_true, Rx2_true_false,
      Rx2_false_true, neg_div, Real.cos_neg, Real.sin_neg, star_complex_ofReal,
      star_complex_I, map_neg, map_mul, neg_neg, neg_mul, mul_neg, Complex.ofReal_neg]

theorem Ry2_conjTranspose (t : ℝ) : (Ry2 t).conjTranspose = Ry2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [conjTranspose_entry, Ry2_false_false, Ry2_true_true, Ry2_true_false,
      Ry2_false_true, neg_div, Real.cos_neg, Real.sin_neg, star_complex_ofReal,
      star_complex_I, map_neg, map_mul, neg_neg, neg_mul, mul_neg, Complex.ofReal_neg]

theorem CRz4_conjTranspose (t : ℝ) : (CRz4 t).conjTranspose = CRz4 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CRz4, conjTranspose_entry4, star_exp]

theorem CRz4_mul (s t : ℝ) : CRz4 s * CRz4 t = CRz4 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul4_apply, CRz4, exp_I_add, exp_neg_I_add] <;>
    (try { congr 1 <;> ring })

theorem Rz2_twoPi : Rz2 (2 * Real.pi) = (-1 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz2, exp_I_pi, exp_neg_I_pi]

theorem Rz2_pi_Z2 : Rz2 Real.pi = (-Complex.I) • Z2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz2, Z2, exp_half_pi_I, exp_neg_half_pi_I]

theorem Rz2_pi_phase_not : ¬ (Rz2 Real.pi = (-Complex.I) • S2) := by
  intro h
  have h1 : (Rz2 Real.pi) true true = Complex.I := by simp [Rz2, exp_half_pi_I]
  have h2 : ((-Complex.I) • S2) true true = (1 : ℂ) := by simp [S2]
  have h3 : (Rz2 Real.pi) true true = ((-Complex.I) • S2) true true := by rw [h]
  rw [h1, h2] at h3
  exact absurd h3 (by norm_num : ¬ (Complex.I : ℂ) = 1)

theorem Rz2_mul (s t : ℝ) : Rz2 s * Rz2 t = Rz2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul2_apply, exp_I_add, exp_neg_I_add]

theorem Rz2_zero : Rz2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem isUnitary_Rz2 (t : ℝ) : IsUnitaryM (Rz2 t) := by
  refine ⟨?_, ?_⟩
  · rw [Rz2_conjTranspose, Rz2_mul, show ((-t : ℝ) + t = 0) by ring, Rz2_zero]
  · rw [Rz2_conjTranspose, Rz2_mul, show ((t : ℝ) + -t = 0) by ring, Rz2_zero]

theorem CRz4_zero : CRz4 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CRz4]

theorem isUnitary_CRz4 (t : ℝ) : IsUnitaryM (CRz4 t) := by
  refine ⟨?_, ?_⟩
  · rw [CRz4_conjTranspose, CRz4_mul, show ((-t : ℝ) + t = 0) by ring, CRz4_zero]
  · rw [CRz4_conjTranspose, CRz4_mul, show ((t : ℝ) + -t = 0) by ring, CRz4_zero]

end
end Quantum
