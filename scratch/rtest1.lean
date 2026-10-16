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

def Ry2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else if x then (Real.sin (t / 2) : ℂ)
    else -(Real.sin (t / 2) : ℂ)

def CRz4 (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x = y then if x.1 then
      Complex.exp (Complex.I * (if x.2 then t / 2 else -(t / 2))) else 1 else 0

/-! TEST A: is Rz2_pi_phase with the real S2 true or false? -/

example : Rz2 Real.pi true true = Complex.I := by
  simp [Rz2]

example : (-Complex.I • S2 : Matrix Bool Bool ℂ) true true = (1 : ℂ) := by
  simp [S2, Pi.smul_apply]

/-! TEST B: entry reductions -/

example (t : ℝ) : Rz2 t false false = Complex.exp (-(Complex.I * (t/2))) := by simp [Rz2]
example (t : ℝ) : Rz2 t true true = Complex.exp (Complex.I * (t/2)) := by simp [Rz2]
example (t : ℝ) : Rz2 t true false = (0:ℂ) := by simp [Rz2]
example (t : ℝ) : Rz2 t false true = (0:ℂ) := by simp [Rz2]

example (t : ℝ) : Rx2 t false false = (Real.cos (t/2) : ℂ) := by simp [Rx2]
example (t : ℝ) : Rx2 t true true = (Real.cos (t/2) : ℂ) := by simp [Rx2]
example (t : ℝ) : Rx2 t true false = -Complex.I * (Real.sin (t/2) : ℂ) := by simp [Rx2]
example (t : ℝ) : Rx2 t false true = -Complex.I * (Real.sin (t/2) : ℂ) := by simp [Rx2]

example (t : ℝ) : Ry2 t false false = (Real.cos (t/2) : ℂ) := by simp [Ry2]
example (t : ℝ) : Ry2 t true true = (Real.cos (t/2) : ℂ) := by simp [Ry2]
example (t : ℝ) : Ry2 t true false = (Real.sin (t/2) : ℂ) := by simp [Ry2]
example (t : ℝ) : Ry2 t false true = -(Real.sin (t/2) : ℂ) := by simp [Ry2]

/-! TEST C: exp helpers -/

example (s t : ℝ) :
    Complex.exp (Complex.I * (s/2)) * Complex.exp (Complex.I * (t/2)) =
      Complex.exp (Complex.I * ((s+t)/2)) := by
  rw [show ((s+t:ℝ)/2) = s/2 + t/2 by ring, mul_add, Complex.exp_add]

example (s t : ℝ) :
    Complex.exp (-(Complex.I * (s/2))) * Complex.exp (-(Complex.I * (t/2))) =
      Complex.exp (-(Complex.I * ((s+t)/2))) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-! TEST D: star of real cast and of -I * real -/

example (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp [Complex.star_def, Complex.conj_ofReal]

example (r : ℝ) : star (-Complex.I * (r : ℂ)) = Complex.I * (r : ℂ) := by
  simp [Complex.star_def, Complex.conj_I, Complex.conj_ofReal, map_mul, map_neg]

example (r : ℝ) : star (-Complex.I * (r : ℂ)) = -(-Complex.I * (r : ℂ)) := by
  simp [Complex.star_def, Complex.conj_I, Complex.conj_ofReal, map_mul, map_neg]

end
end Quantum
