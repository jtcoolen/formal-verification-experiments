import Quantum.Optimizer
open Quantum
set_option maxHeartbeats 400000000
def i0 : Fin 1 := ⟨0, by decide⟩
def sg : List (Gate n) -> Circuit n
  | [] => Circuit.one
  | [g] => Circuit.gate g
  | g :: gs => Circuit.seq (Circuit.gate g) (sg gs)
def cFG : Circuit 1 := sg [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]

theorem ZXZX : Z2 * X2 * Z2 * X2 = (-1 : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z2, X2, mul2_apply]

theorem embed1_smulC {n : Nat} (z : ℂ) (U : Matrix Bool Bool ℂ) (i : Fin n) :
    embed1 (z • U) i = z • embed1 U i := by
  classical
  ext x y
  by_cases h : agreeOff [i] x y <;> simp [embed1_apply, h]

theorem denotationFG : (denote cFG : Operator 1) = (-1 : ℂ) • 1 := by
  classical
  show embed1 Z2 i0 * embed1 X2 i0 * embed1 Z2 i0 * embed1 X2 i0 = (-1 : ℂ) • (1 : Operator 1)
  rw [embed1_mul, embed1_mul, embed1_mul, ZXZX, embed1_smulC, embed1_one]

theorem fg_not_exact : ¬ EqExact cFG (Circuit.one : Circuit 1) := by
  intro h
  have h1 := congrFun (congrFun h (fun _ : Fin 1 => false)) (fun _ : Fin 1 => false)
  rw [denotationFG, denote_one] at h1
  simp only [Matrix.one_apply, Pi.smul_apply, ite_reduce] at h1
  norm_num at h1
