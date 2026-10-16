import Quantum.Rotations
import Quantum.Gates
namespace Quantum
open Complex Real

theorem Rz2_halfPi_S2_test :
    Rz2 (Real.pi / 2) = Complex.exp (-(Complex.I * (Real.pi / 4))) • S2 := by
  have k : Complex.exp (-(Complex.I * (Real.pi / 4))) * Complex.I =
      Complex.exp (Complex.I * (Real.pi / 4)) := by
    have h : Complex.I = Complex.exp (Complex.I * (Real.pi / 2)) := exp_half_pi_I.symm
    rw [h, ← Complex.exp_add]
    congr 1
    ring
  have q : ((Real.pi : ℂ) / 2 / 2) = Real.pi / 4 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz2, S2, k, q]

end Quantum
