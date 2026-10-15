/-
The fixed (non-parameterized) primitive gate matrices, in exact complex arithmetic.

Single-qubit gates are 2x2 matrices indexed by Bool (the computational basis of one qubit,
in the order false = |0>, true = |1>); two-qubit gates are 4x4 matrices indexed by
Bool x Bool (in the order |00>, |01>, |10>, |11>).

Conventions (used consistently throughout the project):
* A matrix entry M x y is the amplitude of the *output* basis state x given the *input*
  basis state y.
* 'seq a b' executes a first and then b, hence 'denote (seq a b) = denote b * denote a'.
* All arithmetic is exact: Real.sqrt 2 and Complex.I are the mathematical real/complex
  operations, never floating point approximations.
-/
import Quantum.MatrixCalc
import Quantum.Angle
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Quantum

open Complex Real

/-! ### Exact constants -/

/-- The exact inverse square root of two, as a complex number. -/
noncomputable def rinv : ℂ := (1 : ℂ) / (Real.sqrt 2 : ℂ)

/-- The exact eighth root of unity omega = (1+i)/sqrt 2, so that T = diag(1, omega). -/
noncomputable def ω : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)

/-- The exact conjugate eighth root of unity, used by T-dagger. -/
noncomputable def ω' : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)

/-- A complex number has unit modulus when its norm square is one.  This is the
representation of "the unit complex numbers" used throughout the project: it is equivalent
to 'Complex.abs z = 1' (since normSq z = ‖z‖²) and is purely algebraic, which makes the
group-theoretic facts about it (inverse, product) immediate. -/
def IsUnitPhase (z : ℂ) : Prop := Complex.normSq z = 1

theorem isUnitPhase_one : IsUnitPhase 1 := by
  show Complex.normSq 1 = 1
  rw [Complex.normSq_one]

theorem isUnitPhase_mul {a b : ℂ} (ha : IsUnitPhase a) (hb : IsUnitPhase b) :
    IsUnitPhase (a * b) := by
  show Complex.normSq (a * b) = 1
  rw [map_mul, ha, hb]
  norm_num

theorem isUnitPhase_neg_one : IsUnitPhase (-1) := by
  show Complex.normSq (-1) = 1
  rw [Complex.normSq_neg, Complex.normSq_one]

theorem isUnitPhase_I : IsUnitPhase Complex.I := by
  show Complex.normSq Complex.I = 1
  norm_num [Complex.normSq_apply, Complex.I_re, Complex.I_im]

theorem isUnitPhase_inv {a : ℂ} (ha : IsUnitPhase a) : IsUnitPhase a⁻¹ := by
  show Complex.normSq a⁻¹ = 1
  rw [Complex.normSq_inv, ha]
  norm_num

theorem isUnitPhase_conj {a : ℂ} (ha : IsUnitPhase a) : IsUnitPhase (star a) := by
  show Complex.normSq (star a) = 1
  rw [Complex.star_def, Complex.normSq_conj, ha]

/-- exp(i t) has unit modulus for every real t. -/
theorem isUnitPhase_exp_I (t : ℝ) : IsUnitPhase (Complex.exp (Complex.I * (t : ℂ))) := by
  show Complex.normSq (Complex.exp (Complex.I * (t : ℂ))) = 1
  rw [Complex.normSq_apply]
  have hre : (Complex.exp (Complex.I * (t : ℂ))).re = Real.cos t := by
    rw [Complex.exp_re, Complex.mul_re, Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Real.exp_zero]
  have him : (Complex.exp (Complex.I * (t : ℂ))).im = Real.sin t := by
    rw [Complex.exp_im, Complex.mul_re, Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Real.exp_zero]
  rw [hre, him]
  rw [show Real.cos t * Real.cos t = Real.cos t ^ 2 by ring,
    show Real.sin t * Real.sin t = Real.sin t ^ 2 by ring]
  rw [Real.cos_sq_add_sin_sq]

theorem sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  intro h
  exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' (Complex.ofReal_eq_zero.mp h)

theorem sqrt2_mul_sqrt2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  show (↑(Real.sqrt 2) : ℂ) * ↑(Real.sqrt 2) = 2
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem rinv_mul_rinv : rinv * rinv = (1 : ℂ) / 2 := by
  show ((1 : ℂ) / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2
  rw [div_mul_div_comm, one_mul, sqrt2_mul_sqrt2]

theorem rinv_ne_zero : rinv ≠ 0 := by
  intro h
  have h2 : rinv * (Real.sqrt 2 : ℂ) = 1 := by
    show ((1 : ℂ) / (Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 1
    rw [div_mul_cancel₀ _ sqrt2_ne_zero]
  rw [h, zero_mul] at h2
  exact zero_ne_one h2

theorem ω_mul_ω : ω * ω = Complex.I := by
  have h1 : (1 + Complex.I) * (1 + Complex.I) = 2 * Complex.I := by
    calc (1 + Complex.I) * (1 + Complex.I)
        = 1 + Complex.I + Complex.I + Complex.I * Complex.I := by ring
      _ = 1 + Complex.I + Complex.I + (-1 : ℂ) := by rw [Complex.I_mul_I]
      _ = 2 * Complex.I := by ring
  show ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) * ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) = Complex.I
  rw [div_mul_div_comm, h1, sqrt2_mul_sqrt2]
  field_simp

theorem ω'_mul_ω' : ω' * ω' = -Complex.I := by
  have h1 : (1 - Complex.I) * (1 - Complex.I) = -(2 * Complex.I) := by
    calc (1 - Complex.I) * (1 - Complex.I)
        = 1 - Complex.I - Complex.I + Complex.I * Complex.I := by ring
      _ = 1 - Complex.I - Complex.I + (-1 : ℂ) := by rw [Complex.I_mul_I]
      _ = -(2 * Complex.I) := by ring
  show ((1 - Complex.I) / (Real.sqrt 2 : ℂ)) * ((1 - Complex.I) / (Real.sqrt 2 : ℂ))
      = -Complex.I
  rw [div_mul_div_comm, h1, sqrt2_mul_sqrt2]
  field_simp

theorem ω_mul_ω' : ω * ω' = 1 := by
  have h1 : (1 + Complex.I) * (1 - Complex.I) = 2 := by
    calc (1 + Complex.I) * (1 - Complex.I) = 1 - Complex.I * Complex.I := by ring
      _ = 1 - (-1 : ℂ) := by rw [Complex.I_mul_I]
      _ = 2 := by ring
  show ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) * ((1 - Complex.I) / (Real.sqrt 2 : ℂ)) = 1
  rw [div_mul_div_comm, h1, sqrt2_mul_sqrt2]
  field_simp

theorem normSq_ω : Complex.normSq ω = 1 := by
  have h1 : Complex.normSq ((1 + Complex.I : ℂ)) = 2 := by
    show (1 + Complex.I).re * (1 + Complex.I).re + (1 + Complex.I).im * (1 + Complex.I).im = 2
    norm_num [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
  have h2 : Complex.normSq ((Real.sqrt 2 : ℂ)) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  show Complex.normSq ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) = 1
  rw [Complex.normSq_div, h1, h2]
  norm_num

theorem normSq_ω' : Complex.normSq ω' = 1 := by
  have h1 : Complex.normSq ((1 - Complex.I : ℂ)) = 2 := by
    show (1 - Complex.I).re * (1 - Complex.I).re + (1 - Complex.I).im * (1 - Complex.I).im = 2
    norm_num [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
  have h2 : Complex.normSq ((Real.sqrt 2 : ℂ)) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  show Complex.normSq ((1 - Complex.I) / (Real.sqrt 2 : ℂ)) = 1
  rw [Complex.normSq_div, h1, h2]
  norm_num

theorem isUnitPhase_ω : IsUnitPhase ω := normSq_ω
theorem isUnitPhase_ω' : IsUnitPhase ω' := normSq_ω'

theorem ω_ne_zero : ω ≠ 0 := by
  intro h
  have h1 := normSq_ω
  rw [h] at h1
  norm_num [Complex.normSq] at h1

/-! ### Single-qubit gate matrices -/

noncomputable section

def H2 : Matrix Bool Bool ℂ := fun x y => if x = y then if x then -rinv else rinv else rinv
def X2 : Matrix Bool Bool ℂ := fun x y => if x = y then 0 else 1
def Y2 : Matrix Bool Bool ℂ := fun x y => if x = y then 0 else if x then Complex.I else -Complex.I
def Z2 : Matrix Bool Bool ℂ := fun x y => if x = y then if x then -1 else 1 else 0
def S2 : Matrix Bool Bool ℂ := fun x y => if x = y then if x then Complex.I else 1 else 0
def T2 : Matrix Bool Bool ℂ := fun x y => if x = y then if x then ω else 1 else 0
def S2Dag : Matrix Bool Bool ℂ := fun x y => if x = y then if x then -Complex.I else 1 else 0
def T2Dag : Matrix Bool Bool ℂ := fun x y => if x = y then if x then ω' else 1 else 0

/-- Controlled-NOT: the control is the first component, the target the second. -/
def CNOT4 : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2 = (if y.1 then !y.2 else y.2) then 1 else 0

/-- Controlled-Z. -/
def CZ4 : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x = y then if x.1 && x.2 then -1 else 1 else 0

/-- SWAP. -/
def SWAP4 : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

end

/-! ### Elementary identities -/

theorem H2_mul_H2 : H2 * H2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, mul2_apply, Pi.one_apply, rinv_mul_rinv] <;> ring_nf <;> simp [rinv_mul_rinv]

theorem X2_mul_X2 : X2 * X2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X2, mul2_apply, Pi.one_apply]

theorem Y2_mul_Y2 : Y2 * Y2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Y2, mul2_apply, Pi.one_apply, Complex.I_mul_I] <;> ring_nf <;> norm_num

theorem Z2_mul_Z2 : Z2 * Z2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z2, mul2_apply, Pi.one_apply]

theorem S2_mul_S2 : S2 * S2 = Z2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S2, Z2, mul2_apply, Complex.I_mul_I] <;> ring_nf <;> norm_num

theorem T2_mul_T2 : T2 * T2 = S2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T2, S2, mul2_apply, ω_mul_ω]

theorem S2Dag_mul_S2 : S2Dag * S2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S2Dag, S2, mul2_apply, Pi.one_apply, Complex.I_mul_I] <;> ring_nf <;> norm_num

theorem S2_mul_S2Dag : S2 * S2Dag = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S2Dag, S2, mul2_apply, Pi.one_apply, Complex.I_mul_I] <;> ring_nf <;> norm_num

theorem T2Dag_mul_T2 : T2Dag * T2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T2Dag, T2, mul2_apply, Pi.one_apply, ω_mul_ω', mul_comm]

theorem T2_mul_T2Dag : T2 * T2Dag = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T2Dag, T2, mul2_apply, Pi.one_apply, ω_mul_ω', mul_comm]

theorem H2_mul_X2_mul_H2 : H2 * X2 * H2 = Z2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mul2_apply, sum_bool_eq, H2, X2, Z2, rinv_mul_rinv, rinv_ne_zero] <;>
    ring_nf <;> simp [rinv_mul_rinv]

theorem H2_mul_Z2_mul_H2 : H2 * Z2 * H2 = X2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mul2_apply, sum_bool_eq, H2, X2, Z2, rinv_mul_rinv, rinv_ne_zero] <;>
    ring_nf <;> simp [rinv_mul_rinv]

/-- Pauli X and Z anticommute: the two products differ by the global phase -1. -/
theorem X2_mul_Z2_phase : X2 * Z2 = (-1 : ℂ) • (Z2 * X2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X2, Z2, mul2_apply, smul_eq_mul, mul_neg, neg_mul, neg_neg] <;> ring_nf <;> norm_num

theorem X2_mul_Y2_phase : X2 * Y2 = (-1 : ℂ) • (Y2 * X2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X2, Y2, mul2_apply, smul_eq_mul, Complex.I_mul_I] <;> ring_nf <;> norm_num

theorem Y2_mul_Z2_phase : Y2 * Z2 = (-1 : ℂ) • (Z2 * Y2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Y2, Z2, mul2_apply, smul_eq_mul, Complex.I_mul_I] <;> ring_nf <;> norm_num

/-! ### Two-qubit identities -/

theorem CNOT4_mul_CNOT4 : CNOT4 * CNOT4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CNOT4, mul4_apply, Pi.one_apply]

theorem CZ4_mul_CZ4 : CZ4 * CZ4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CZ4, mul4_apply, Pi.one_apply]

theorem SWAP4_mul_SWAP4 : SWAP4 * SWAP4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SWAP4, mul4_apply, Pi.one_apply]

/-! ### Adjointness and unitarity of the primitives -/

theorem isUnitary_H2 : IsUnitaryM H2 := by
  have hc : H2.conjTranspose = H2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H2, conjTranspose_entry, rinv, star_def]
  constructor
  · rw [hc]; exact H2_mul_H2
  · rw [hc]; exact H2_mul_H2

theorem isUnitary_X2 : IsUnitaryM X2 := by
  have hc : X2.conjTranspose = X2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X2, conjTranspose_entry]
  constructor
  · rw [hc]; exact X2_mul_X2
  · rw [hc]; exact X2_mul_X2

theorem isUnitary_Y2 : IsUnitaryM Y2 := by
  have hc : Y2.conjTranspose = Y2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Y2, conjTranspose_entry, star_def, Complex.ext_iff, Complex.I_mul_I] <;>
      ring_nf <;> simp
  constructor
  · rw [hc]; exact Y2_mul_Y2
  · rw [hc]; exact Y2_mul_Y2

theorem isUnitary_Z2 : IsUnitaryM Z2 := by
  have hc : Z2.conjTranspose = Z2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z2, conjTranspose_entry]
  constructor
  · rw [hc]; exact Z2_mul_Z2
  · rw [hc]; exact Z2_mul_Z2

theorem S2Dag_eq_conjTranspose : S2Dag = S2.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S2Dag, S2, conjTranspose_entry, star_def, Complex.ext_iff] <;>
    ring_nf <;> simp

theorem T2Dag_eq_conjTranspose : T2Dag = T2.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T2Dag, T2, ω, ω', conjTranspose_entry, star_def, Complex.ext_iff, Complex.div_re,
      Complex.div_im, Complex.normSq_ofReal] <;>
    field_simp <;> norm_num

theorem S2_eq_conjTranspose_S2Dag : S2 = S2Dag.conjTranspose := by
  rw [S2Dag_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem T2_eq_conjTranspose_T2Dag : T2 = T2Dag.conjTranspose := by
  rw [T2Dag_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem isUnitary_S2 : IsUnitaryM S2 := by
  constructor
  · rw [← S2Dag_eq_conjTranspose]; exact S2_mul_S2Dag
  · rw [← S2Dag_eq_conjTranspose]; exact S2Dag_mul_S2

theorem isUnitary_T2 : IsUnitaryM T2 := by
  constructor
  · rw [← T2Dag_eq_conjTranspose]; exact T2_mul_T2Dag
  · rw [← T2Dag_eq_conjTranspose]; exact T2Dag_mul_T2

theorem isUnitary_S2Dag : IsUnitaryM S2Dag := by
  constructor
  · rw [← S2_eq_conjTranspose_S2Dag]; exact S2Dag_mul_S2
  · rw [← S2_eq_conjTranspose_S2Dag]; exact S2_mul_S2Dag

theorem isUnitary_T2Dag : IsUnitaryM T2Dag := by
  constructor
  · rw [← T2_eq_conjTranspose_T2Dag]; exact T2Dag_mul_T2
  · rw [← T2_eq_conjTranspose_T2Dag]; exact T2_mul_T2Dag

theorem isUnitary_CNOT4 : IsUnitaryM CNOT4 := by
  have hc : CNOT4.conjTranspose = CNOT4 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CNOT4, conjTranspose_entry4]
  constructor
  · rw [hc]; exact CNOT4_mul_CNOT4
  · rw [hc]; exact CNOT4_mul_CNOT4

theorem isUnitary_CZ4 : IsUnitaryM CZ4 := by
  have hc : CZ4.conjTranspose = CZ4 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CZ4, conjTranspose_entry4]
  constructor
  · rw [hc]; exact CZ4_mul_CZ4
  · rw [hc]; exact CZ4_mul_CZ4

theorem isUnitary_SWAP4 : IsUnitaryM SWAP4 := by
  have hc : SWAP4.conjTranspose = SWAP4 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SWAP4, conjTranspose_entry4]
  constructor
  · rw [hc]; exact SWAP4_mul_SWAP4
  · rw [hc]; exact SWAP4_mul_SWAP4

/-! ### The specified action of each primitive gate on computational basis states -/

theorem X2_action (x y : Bool) : X2 x y = if x = !y then (1 : ℂ) else 0 := by
  cases x <;> cases y <;> simp [X2]

theorem Z2_action (x y : Bool) : Z2 x y = if x = y then (if x then (-1 : ℂ) else 1) else 0 := rfl

theorem H2_action (x y : Bool) :
    H2 x y = if x = y then (if x then -rinv else rinv) else rinv := rfl

theorem CNOT4_action (x y : Bool × Bool) :
    CNOT4 x y = if x = (y.1, if y.1 then !y.2 else y.2) then (1 : ℂ) else 0 := by
  cases x <;> cases y <;> simp [CNOT4]

theorem SWAP4_action (x y : Bool × Bool) :
    SWAP4 x y = if x = (y.2, y.1) then (1 : ℂ) else 0 := by
  cases x <;> cases y <;> simp [SWAP4]

end Quantum