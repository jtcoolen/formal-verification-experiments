import Quantum.Rotations
import Quantum.Gates
namespace Quantum
open Complex Real

lemma key_test : Complex.exp (-(Complex.I * (Real.pi / 4))) * Complex.I =
    Complex.exp (Complex.I * (Real.pi / 4)) := by
  rw [← exp_half_pi_I, ← Complex.exp_add]
  congr 1
  ring

theorem Rz2_halfPi_S2 :
    Rz2 (Real.pi / 2) = Complex.exp (-(Complex.I * (Real.pi / 4))) • S2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz2, S2, key_test, exp_neg_I_pi_div_two_stub]

end Quantum
