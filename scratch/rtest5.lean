import Quantum.MatrixCalc
import Quantum.Angle
import Quantum.Gates
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Quantum
open Complex Real
noncomputable section

def Rx2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else -Complex.I * (Real.sin (t / 2) : ℂ)
def Ry2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else if x then (Real.sin (t / 2) : ℂ)
    else -(Real.sin (t / 2) : ℂ)

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
lemma star_exp (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  rw [Complex.star_def, ← Complex.exp_conj]

/- variants for pushing star -/
example (x : ℂ) : star (-x) = -star x := by simp
example (x y : ℂ) : star (x * y) = star x * star y := by simp
example (x : ℂ) : star (x / 2) = star x / 2 := by simp
example (z : ℂ) : star (Complex.cos z) = Complex.cos (star z) := by
  rw [Complex.star_def, ← Complex.cos_conj]
example (z : ℂ) : star (Complex.sin z) = Complex.sin (star z) := by
  rw [Complex.star_def, ← Complex.sin_conj]
example : (Complex.I : ℂ) ≠ 1 := by norm_num
example : (Complex.I : ℂ) ≠ 1 := by simp
example : ¬ (Complex.I : ℂ) = 1 := by intro h; exact absurd (congrArg Complex.re h) (by norm_num)

theorem Rx2_conjTranspose (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx2, neg_div, star_cos_stub, star_sin_stub]

@[simp] lemma star_cos_stub (z : ℂ) : star (Complex.cos z) = Complex.cos (star z) := by
  rw [Complex.star_def, ← Complex.cos_conj]
@[simp] lemma star_sin_stub (z : ℂ) : star (Complex.sin z) = Complex.sin (star z) := by
  rw [Complex.star_def, ← Complex.sin_conj]

theorem Rx2_conjTranspose2 (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx2, neg_div, star_cos_stub, star_sin_stub]

theorem Ry2_conjTranspose2 (t : ℝ) : (Ry2 t).conjTranspose = Ry2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry2, neg_div, star_cos_stub, star_sin_stub]

theorem Rx2_conjTranspose3 (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [conjTranspose_entry, Rx2_false_false, Rx2_true_true, Rx2_true_false,
      Rx2_false_true, neg_div, Real.cos_neg, Real.sin_neg, star_complex_ofReal,
      star_complex_I, neg_neg, neg_mul, mul_neg, Complex.ofReal_neg, map_neg, map_mul]

theorem Ry2_conjTranspose3 (t : ℝ) : (Ry2 t).conjTranspose = Ry2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [conjTranspose_entry, Ry2_false_false, Ry2_true_true, Ry2_true_false,
      Ry2_false_true, neg_div, Real.cos_neg, Real.sin_neg, star_complex_ofReal,
      star_complex_I, neg_neg, neg_mul, mul_neg, Complex.ofReal_neg, map_neg, map_mul]

end
end Quantum
