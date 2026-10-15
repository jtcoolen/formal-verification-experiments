/-
Parameterized rotation gate matrices, in exact complex arithmetic.

Rz(theta) = diag(exp(-i theta/2), exp(i theta/2)), Rx(theta) = cos(theta/2) I - i sin(theta/2) X,
Ry(theta) = cos(theta/2) I - i sin(theta/2) Y, and CRz(theta) the controlled version of Rz.
Angles are exact (Quantum.Angle): a rational number of radians plus a rational multiple of pi.
-/
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

/-- Rx(theta) = cos(theta/2) I - i sin(theta/2) X, exactly. -/

def Rx2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else -Complex.I * (Real.sin (t / 2) : ℂ)

/-- Ry(theta) = cos(theta/2) I - i sin(theta/2) Y, exactly. -/

def Ry2 (t : ℝ) : Matrix Bool Bool ℂ :=
  fun x y => if x = y then (Real.cos (t / 2) : ℂ) else if x then (Real.sin (t / 2) : ℂ)
    else -(Real.sin (t / 2) : ℂ)

/-! ### Two-qubit gate matrices -/

/-- Controlled-Rz: the control is the first component, the target the second. -/

def CRz4 (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x = y then if x.1 then
      Complex.exp (Complex.I * (if x.2 then t / 2 else -(t / 2))) else 1 else 0

end

/-! ### Entrywise form of the rotation matrices

The definitions above hide the angle inside a `Bool`-valued test.  These lemmas expose each
individual entry in the shape the proofs below consume. -/

@[simp] lemma Rz2_false_false (t : ℝ) :
    Rz2 t false false = Complex.exp (-(Complex.I * (t / 2))) := by simp [Rz2]
@[simp] lemma Rz2_true_true (t : ℝ) :
    Rz2 t true true = Complex.exp (Complex.I * (t / 2)) := by simp [Rz2]
@[simp] lemma Rz2_true_false (t : ℝ) : Rz2 t true false = 0 := by simp [Rz2]
@[simp] lemma Rz2_false_true (t : ℝ) : Rz2 t false true = 0 := by simp [Rz2]

@[simp] lemma Rx2_false_false (t : ℝ) : Rx2 t false false = (Real.cos (t / 2) : ℂ) := by
  simp [Rx2]
@[simp] lemma Rx2_true_true (t : ℝ) : Rx2 t true true = (Real.cos (t / 2) : ℂ) := by
  simp [Rx2]
@[simp] lemma Rx2_true_false (t : ℝ) :
    Rx2 t true false = -Complex.I * (Real.sin (t / 2) : ℂ) := by simp [Rx2]
@[simp] lemma Rx2_false_true (t : ℝ) :
    Rx2 t false true = -Complex.I * (Real.sin (t / 2) : ℂ) := by simp [Rx2]

@[simp] lemma Ry2_false_false (t : ℝ) : Ry2 t false false = (Real.cos (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_true_true (t : ℝ) : Ry2 t true true = (Real.cos (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_true_false (t : ℝ) : Ry2 t true false = (Real.sin (t / 2) : ℂ) := by
  simp [Ry2]
@[simp] lemma Ry2_false_true (t : ℝ) : Ry2 t false true = -(Real.sin (t / 2) : ℂ) := by
  simp [Ry2]

/-! ### Elementary phase arithmetic -/

/-- Half-angle bookkeeping over the reals. -/
lemma half_add (s t : ℝ) : ((s + t : ℝ) / 2) = s / 2 + t / 2 := by ring

/-- Two pure phases add: `exp (i s/2) * exp (i t/2) = exp (i (s+t)/2)`. -/
lemma exp_I_add (s t : ℝ) :
    Complex.exp (Complex.I * (s / 2)) * Complex.exp (Complex.I * (t / 2)) =
      Complex.exp (Complex.I * ((s + t) / 2)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The same identity for the lower diagonal entry, whose phase is negated. -/
lemma exp_neg_I_add (s t : ℝ) :
    Complex.exp (-(Complex.I * (s / 2))) * Complex.exp (-(Complex.I * (t / 2))) =
      Complex.exp (-(Complex.I * ((s + t) / 2))) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The two off-diagonal factors of `Rx2` multiply to a real number. -/
lemma neg_I_mul_neg_I (x y : ℂ) : (-Complex.I * x) * (-Complex.I * y) = -(x * y) := by
  calc (-Complex.I * x) * (-Complex.I * y) = (Complex.I * Complex.I) * (x * y) := by ring
    _ = (-1 : ℂ) * (x * y) := by rw [Complex.I_mul_I]
    _ = -(x * y) := by ring

/-- Conjugation commutes with the complex exponential. -/
lemma star_exp (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  rw [Complex.star_def, ← Complex.exp_conj]

/-- Conjugation commutes with the complex cosine and sine. -/
lemma star_cos (z : ℂ) : star (Complex.cos z) = Complex.cos (star z) := by
  rw [Complex.star_def, ← Complex.cos_conj]

lemma star_sin (z : ℂ) : star (Complex.sin z) = Complex.sin (star z) := by
  rw [Complex.star_def, ← Complex.sin_conj]

/-- The phases of `Rz` at the two angles of interest, in the orientation (`i` on the left)
that the entries of `Rz2` use. -/
lemma exp_I_pi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
  rw [show Complex.I * (Real.pi : ℂ) = Real.pi * Complex.I by ring, exp_pi_I]

lemma exp_neg_I_pi : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
  rw [show -(Complex.I * (Real.pi : ℂ)) = -(Real.pi * Complex.I) by ring, exp_neg_pi_I]

/-! ### Elementary identities -/

theorem Rz2_mul (s t : ℝ) : Rz2 s * Rz2 t = Rz2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul2_apply, exp_I_add, exp_neg_I_add]

theorem Rz2_zero : Rz2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Rz(2 pi) is *not* the identity: it is the identity times the global phase -1. -/

theorem Rz2_twoPi : Rz2 (2 * Real.pi) = (-1 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz2, exp_I_pi, exp_neg_I_pi]

theorem Rx2_mul (s t : ℝ) : Rx2 s * Rx2 t = Rx2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul2_apply, Rx2_false_false, Rx2_true_true, Rx2_true_false, Rx2_false_true,
      neg_I_mul_neg_I, half_add, Real.cos_add, Real.sin_add] <;>
    push_cast <;> ring

theorem Rx2_zero : Rx2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rx2, Real.cos_zero, Real.sin_zero]

theorem Ry2_mul (s t : ℝ) : Ry2 s * Ry2 t = Ry2 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul2_apply, Ry2_false_false, Ry2_true_true, Ry2_true_false, Ry2_false_true,
      half_add, Real.cos_add, Real.sin_add] <;>
    push_cast <;> ring

theorem Ry2_zero : Ry2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ry2, Real.cos_zero, Real.sin_zero]

/-- Rz(pi) equals the Pauli Z gate up to the global phase -i.

This is the true statement of the `Rz(pi) = global phase * gate` family: see the note
after `isUnitary_CRz4` for why the requested variant with the phase gate `S2` is false. -/
theorem Rz2_pi_Z2 : Rz2 Real.pi = (-Complex.I) • Z2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz2, Z2, exp_half_pi_I, exp_neg_half_pi_I]

/-! ### Two-qubit identities -/

theorem CRz4_mul (s t : ℝ) : CRz4 s * CRz4 t = CRz4 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul4_apply, CRz4, exp_I_add, exp_neg_I_add]

theorem CRz4_zero : CRz4 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CRz4]

/-! ### Adjointness and unitarity of the primitives -/

/-- A square complex matrix is unitary when multiplying by its conjugate transpose gives the
identity in both orders. -/

theorem Rz2_conjTranspose (t : ℝ) : (Rz2 t).conjTranspose = Rz2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz2, star_exp, neg_div]

theorem Rx2_conjTranspose (t : ℝ) : (Rx2 t).conjTranspose = Rx2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rx2, neg_div, star_cos, star_sin]

theorem Ry2_conjTranspose (t : ℝ) : (Ry2 t).conjTranspose = Ry2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ry2, neg_div, star_cos, star_sin]

theorem isUnitary_Rz2 (t : ℝ) : IsUnitaryM (Rz2 t) := by
  refine ⟨?_, ?_⟩
  · rw [Rz2_conjTranspose, Rz2_mul, show ((t : ℝ) + -t = 0) by ring, Rz2_zero]
  · rw [Rz2_conjTranspose, Rz2_mul, show ((-t : ℝ) + t = 0) by ring, Rz2_zero]

theorem isUnitary_Rx2 (t : ℝ) : IsUnitaryM (Rx2 t) := by
  refine ⟨?_, ?_⟩
  · rw [Rx2_conjTranspose, Rx2_mul, show ((t : ℝ) + -t = 0) by ring, Rx2_zero]
  · rw [Rx2_conjTranspose, Rx2_mul, show ((-t : ℝ) + t = 0) by ring, Rx2_zero]

theorem isUnitary_Ry2 (t : ℝ) : IsUnitaryM (Ry2 t) := by
  refine ⟨?_, ?_⟩
  · rw [Ry2_conjTranspose, Ry2_mul, show ((t : ℝ) + -t = 0) by ring, Ry2_zero]
  · rw [Ry2_conjTranspose, Ry2_mul, show ((-t : ℝ) + t = 0) by ring, Ry2_zero]

theorem CRz4_conjTranspose (t : ℝ) : (CRz4 t).conjTranspose = CRz4 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CRz4, star_exp, neg_div]

theorem isUnitary_CRz4 (t : ℝ) : IsUnitaryM (CRz4 t) := by
  refine ⟨?_, ?_⟩
  · rw [CRz4_conjTranspose, CRz4_mul, show ((t : ℝ) + -t = 0) by ring, CRz4_zero]
  · rw [CRz4_conjTranspose, CRz4_mul, show ((-t : ℝ) + t = 0) by ring, CRz4_zero]

/-! ### A note on the requested identity `Rz2 Real.pi = (-Complex.I) • S2`

The statement

    theorem Rz2_pi_phase : Rz2 Real.pi = (-Complex.I) • S2

that this file was originally given with is *false*, so it is not proved here (and it must
not be weakened into something else in order to fake a proof).  The two matrices disagree
already on the `(true, true)` entry:

    Rz2 Real.pi true true       = exp (i * pi / 2)          = i
    ((-Complex.I) • S2) true true = (-i) * S2 true true     = (-i) * i = 1

and `i ≠ (1 : ℂ)`; the machine-checked disproof is `Rz2_pi_phase_not` below.  The true
global-phase statements in this family are `Rz2_pi_Z2` above (Rz(pi) = -i * Z) and
`Rz2_halfPi_S2` below: the phase gate `S` is `Rz(pi/2)`, not `Rz pi`, up to the global
phase `exp (-i pi / 4)`.
-/

/-- The correct global-phase identity relating `Rz` to the phase gate `S`. -/
theorem Rz2_halfPi_S2 :
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

/-- Machine-checked refutation of `Rz2 Real.pi = (-Complex.I) • S2`. -/
theorem Rz2_pi_phase_not : ¬ (Rz2 Real.pi = (-Complex.I) • S2) := by
  intro h
  have h1 : (Rz2 Real.pi) true true = Complex.I := by simp [Rz2, exp_half_pi_I]
  have h2 : ((-Complex.I) • S2) true true = (1 : ℂ) := by simp [S2]
  have h3 : (Rz2 Real.pi) true true = ((-Complex.I) • S2) true true := by rw [h]
  rw [h1, h2] at h3
  exact absurd h3 (by intro hh; exact absurd (congrArg Complex.re hh) (by norm_num))

end Quantum
