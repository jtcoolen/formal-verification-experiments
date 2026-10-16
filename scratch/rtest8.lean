import Quantum.Rotations
import Quantum.Gates
namespace Quantum
open Complex Real

theorem Rz2_halfPi_S2_test :
    Rz2 (Real.pi / 2) = Complex.exp (-(Complex.I * (Real.pi / 4))) • S2 := by
  have k : Complex.exp (Complex.I * (Real.pi / 4)) =
      Complex.exp (-(Complex.I * (Real.pi / 4))) * Complex.I := by
    have h : Complex.exp (-(Complex.I * (Real.pi / 4))) *
        Complex.exp (Complex.I * (Real.pi / 2)) =
        Complex.exp (Complex.I * (Real.pi / 4)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [exp_half_pi_I] at h
    exact h.symm
  have q : ((Real.pi : ℂ) / 2 / 2) = Real.pi / 4 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz2, S2, k, q]

end Quantum
