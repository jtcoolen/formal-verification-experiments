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

def Rx2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else -Complex.I * (Real.sin (t / 2) : ℂ)

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

/- (a) smul on the identity matrix -/
example : ((-1 : ℂ) • (1 : Matrix Bool Bool ℂ)) true true = (-1 : ℂ) := by simp
example : ((-1 : ℂ) • (1 : Matrix Bool Bool ℂ)) true false = (-1 : ℂ) := by simp

theorem t_twoPi : Rz2 (2 * Real.pi) = (-1 : ℂ) • 1 := by
  have h1 : Complex.I * ((2 * Real.pi : ℝ) / 2) = Complex.I * (Real.pi : ℂ) := by
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, exp_I_pi, exp_neg_I_pi]

/- (b) Rx2 conjTranspose: star of cos/sin -/
example (t : ℝ) : star (Rx2 t false false) = Rx2 (-t) false false := by
  simp [Rx2, neg_div]

example (t : ℝ) : star (Rx2 t false false) = Rx2 (-t) false false := by
  simp [Rx2, conjTranspose_entry, neg_div, Complex.conj_cos]

example (t : ℝ) : star (Rx2 t true false) = Rx2 (-t) false true := by
  simp [Rx2, neg_div, Complex.conj_sin]

example (t : ℝ) : star (Rx2 t true false) = Rx2 (-t) false true := by
  simp [Rx2, neg_div, Complex.conj_sin, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_div]

theorem t_Rx2_conj (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx2, neg_div, Complex.conj_cos, Complex.conj_sin, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_div, map_neg, map_mul]

theorem t_Rz2_conj (t : ℝ) : (Rz2 t).conjTranspose = Rz2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz2, neg_div]

/- (c) IsUnitaryM via refine angle brackets -/
theorem t_isUnitary (t : ℝ) : IsUnitaryM (Rz2 t) := by
  refine ⟨?_, ?_⟩
  · rw [Rz2_conj_stub, Rz2_mul_stub, neg_add_self, Rz2_zero_stub]
  · rw [Rz2_conj_stub, Rz2_mul_stub, add_right_neg, Rz2_zero_stub]

lemma Rz2_conj_stub (t : ℝ) : (Rz2 t).conjTranspose = Rz2 (-t) := t_Rz2_conj t
lemma Rz2_mul_stub (s t : ℝ) : Rz2 s * Rz2 t = Rz2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul2_apply, exp_I_add, exp_neg_I_add]
lemma Rz2_zero_stub : Rz2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem t_isUnitary2 (t : ℝ) : IsUnitaryM (Rz2 t) := by
  refine ⟨?_, ?_⟩
  · rw [Rz2_conj_stub, Rz2_mul_stub, neg_add_self, Rz2_zero_stub]
  · rw [Rz2_conj_stub, Rz2_mul_stub, add_right_neg, Rz2_zero_stub]

theorem t_isUnitary3 (t : ℝ) : IsUnitaryM (Rz2 t) := by
  rw [Rz2_conj_stub]
  exact ⟨by rw [Rz2_mul_stub, neg_add_self, Rz2_zero_stub],
    by rw [Rz2_mul_stub, add_right_neg, Rz2_zero_stub]⟩

end
end Quantum
