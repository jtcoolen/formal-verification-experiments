/-
Global phase and controlled operations.

Equivalence modulo global phase is NOT preserved when an operation is turned into a
controlled operation.  This module proves both halves of that statement inside the matrix
semantics, using the primitive CRz gate of the language:

* Rz(2*pi) is phase-equivalent to the identity (global phase -1), and is provably NOT equal
  to it, so the phase is genuinely present;
* CRz(2*pi) is NOT phase-equivalent to the identity.

Consequently the circuit language deliberately has no constructor that controls an arbitrary
subcircuit: the only contexts in which phase-equivalence may be used are the sequential
contexts of Quantum/Contexts.lean, and every controlled gate (CNOT, CZ, CRz) has its own
independent matrix semantics and its own proved rewrite rules.
-/
import Quantum.Semantics
import Quantum.Equivalence

namespace Quantum
namespace ControlPhase

open Classical

/-- The basis state that is 1 exactly at qubit i. -/
def oneHot {n : Nat} (i : Fin n) : Basis n := fun a => if a = i then true else false

@[simp] theorem oneHot_same {n : Nat} (i : Fin n) : oneHot i i = true := if_pos rfl

theorem oneHot_ne {n : Nat} {i a : Fin n} (h : ¬ a = i) : oneHot i a = false := if_neg h

/-- The all-zero basis state. -/
def zeroB {n : Nat} : Basis n := fun _ => false

theorem agreeOff_refl {n : Nat} (s : List (Fin n)) (x : Basis n) : agreeOff s x x :=
  fun a ha => rfl

@[simp] theorem CRz4_false_false (t : ℝ) : CRz4 t (false, false) (false, false) = 1 := by
  simp [CRz4]

@[simp] theorem CRz4_true_false (t : ℝ) :
    CRz4 t (true, false) (true, false) = Complex.exp (-(Complex.I * (t / 2))) := by
  simp [CRz4]

/-- Rz(2 pi) is equivalent to the identity modulo the global phase -1. -/
theorem rz_twoPi_phase_one {n : Nat} (i : Fin n) :
    PhaseEquivalent (Circuit.gate (Gate.rz i Angle.twoPi)) Circuit.one := by
  refine ⟨(-1 : ℂ), isUnitPhase_neg_one, ?_⟩
  show embed1 (Rz2 (Angle.val Angle.twoPi)) i = (-1 : ℂ) • (1 : Operator n)
  rw [Angle.val_twoPi, Rz2_twoPi, embed1_smul, embed1_one]

/-- Rz(2 pi) is NOT equal to the identity: the global phase is genuinely present. -/
theorem rz_twoPi_ne_one {n : Nat} (i : Fin n) :
    ¬ (denote (Circuit.gate (Gate.rz i Angle.twoPi)) = (1 : Operator n)) := by
  classical
  intro h
  have h1 : (denote (Circuit.gate (Gate.rz i Angle.twoPi)) : Operator n) (oneHot i) (oneHot i)
      = -1 := by
    show embed1 (Rz2 (Angle.val Angle.twoPi)) i (oneHot i) (oneHot i) = -1
    rw [embed1_eq_of_agree _ _ (agreeOff_refl [i] (oneHot i))]
    rw [oneHot_same, Rz2_true_true, Angle.val_twoPi]
    rw [show ((2 * Real.pi : ℝ) : ℂ) / 2 = (Real.pi : ℂ) by push_cast; ring]
    rw [exp_I_pi]
  have h2 : ((1 : Operator n) : Operator n) (oneHot i) (oneHot i) = 1 := by
    simp only [Matrix.one_apply]
    simp
  have := congrFun (congrFun h (oneHot i)) (oneHot i)
  rw [h1, h2] at this
  exact absurd this (by norm_num)

/-- The two relevant diagonal entries of CRz(2 pi). -/
theorem crz_twoPi_entries {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    (denote (Circuit.gate (Gate.crz i j hij Angle.twoPi)) : Operator n) (zeroB) (zeroB) = 1 /\
    (denote (Circuit.gate (Gate.crz i j hij Angle.twoPi)) : Operator n) (oneHot i) (oneHot i)
      = -1 := by
  classical
  constructor
  · show embed2 (CRz4 (Angle.val Angle.twoPi)) i j zeroB zeroB = 1
    rw [embed2_eq_of_agree _ _ _ (agreeOff_refl [i, j] zeroB), Angle.val_twoPi]
    show CRz4 (2 * Real.pi) (false, false) (false, false) = 1
    rw [CRz4_false_false]
  · show embed2 (CRz4 (Angle.val Angle.twoPi)) i j (oneHot i) (oneHot i) = -1
    rw [embed2_eq_of_agree _ _ _ (agreeOff_refl [i, j] (oneHot i)), Angle.val_twoPi]
    show CRz4 (2 * Real.pi) (oneHot i i, oneHot i j) (oneHot i i, oneHot i j) = -1
    rw [oneHot_same, oneHot_ne (Ne.symm hij)]
    rw [CRz4_true_false]
    rw [show ((2 * Real.pi : ℝ) : ℂ) / 2 = (Real.pi : ℂ) by push_cast; ring]
    rw [exp_neg_I_pi]

/-- CRz(2 pi) is NOT equivalent to the identity modulo global phase. -/
theorem crz_twoPi_not_phase_one {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    ¬ PhaseEquivalent (Circuit.gate (Gate.crz i j hij Angle.twoPi)) Circuit.one := by
  classical
  rintro ⟨z, hz, he⟩
  obtain ⟨h1, h2⟩ := crz_twoPi_entries hij
  have e1 : (z • denote (Circuit.one : Circuit n)) zeroB zeroB = z := by
    show z * (1 : Operator n) zeroB zeroB = z
    rw [Matrix.one_apply]
    simp
  have e2 : (z • denote (Circuit.one : Circuit n)) (oneHot i) (oneHot i) = z := by
    show z * (1 : Operator n) (oneHot i) (oneHot i) = z
    rw [Matrix.one_apply]
    simp
  have h1' := congrFun (congrFun he zeroB) zeroB
  have h2' := congrFun (congrFun he (oneHot i)) (oneHot i)
  rw [e1, h1] at h1'
  rw [e2, h2] at h2'
  have hz1 : (1 : ℂ) = z := h1'
  have hzm1 : (-1 : ℂ) = z := h2'
  have hcontra : (1 : ℂ) = -1 := hz1.trans hzm1.symm
  exact absurd hcontra (by norm_num)

/-- Controlled formation preserves *exact* equality: CZ ; CZ = I holds exactly, and this is
the kind of identity that may safely be used under a control. -/
theorem cz_cz_eq_one {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    EqExact (Circuit.seq (Circuit.gate (Gate.cz i j hij)) (Circuit.gate (Gate.cz i j hij)))
      Circuit.one := by
  show embed2 CZ4 i j * embed2 CZ4 i j = 1
  rw [embed2_mul (hij := hij), CZ4_mul_CZ4, embed2_one hij]

end ControlPhase
end Quantum