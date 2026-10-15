import Quantum
set_option maxHeartbeats 20000000
example : (1/4 : ℚ) + 1/4 = 1/2 := by norm_num
example : (⟨100000000000000000, 0⟩ : ℚ) + 0 = 100000000000000000 := by norm_num
example : ((2147483647 : ℚ) / 4294967295) + ((2147483648 : ℚ) / 4294967297) ≠ 0 := by norm_num
example : (100 : ℚ) * (1/100 : ℚ) = 1 := by norm_num
open Quantum
example : (⟨0,1⟩:Angle) + (⟨0,-1⟩:Angle) = 0 := by
  apply Angle.eq_of_components <;> simp [Angle.add_rat, Angle.add_piQ] <;> norm_num
