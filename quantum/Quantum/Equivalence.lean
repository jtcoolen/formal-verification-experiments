/-
Equivalence of circuits modulo global phase, and exact semantic equality.

Two circuits are equivalent modulo global phase when their denotations differ by
multiplication by a complex number of unit modulus.  This file proves that the relation is
an equivalence relation and identifies exactly which circuit contexts preserve it.

The representation of "unit complex number" is 'IsUnitPhase z : Complex.normSq z = 1',
which is equivalent to 'Complex.abs z = 1' and is purely algebraic.

IMPORTANT (see Quantum/ControlPhase.lean): equivalence modulo global phase is NOT preserved
by turning an operation into a controlled operation.  The contexts for which congruence is
proved here are therefore exactly the sequential contexts of Quantum/Contexts.lean; no
constructor controls an arbitrary subcircuit.
-/
import Quantum.Semantics

namespace Quantum

/-- Two n-qubit circuits are equivalent modulo global phase when their denotations differ by
a scalar of unit modulus. -/
def PhaseEquivalent {n : Nat} (a b : Circuit n) : Prop :=
  ∃ z : ℂ, IsUnitPhase z ∧ denote a = z • denote b

/-- Exact semantic equality (no phase allowed). -/
def EqExact {n : Nat} (a b : Circuit n) : Prop := denote a = denote b

namespace PhaseEquivalent

theorem refl {n : Nat} (a : Circuit n) : PhaseEquivalent a a :=
  ⟨1, isUnitPhase_one, by simp⟩

theorem eq_zero {n : Nat} {a b : Circuit n} (h : PhaseEquivalent a b) :
    ∃ z : ℂ, IsUnitPhase z ∧ denote a = z • denote b := h

theorem symm {n : Nat} {a b : Circuit n} (h : PhaseEquivalent a b) : PhaseEquivalent b a := by
  classical
  obtain ⟨z, hz, he⟩ := h
  refine ⟨z⁻¹, isUnitPhase_inv hz, ?_⟩
  rw [he]
  rw [smul_smul]
  have hz0 : z ≠ 0 := by
    intro hh; rw [hh] at hz; norm_num [IsUnitPhase, Complex.normSq] at hz
  rw [inv_mul_cancel₀ hz0]
  simp

theorem trans {n : Nat} {a b c : Circuit n} (h₁ : PhaseEquivalent a b)
    (h₂ : PhaseEquivalent b c) : PhaseEquivalent a c := by
  obtain ⟨z, hz, he₁⟩ := h₁
  obtain ⟨w, hw, he₂⟩ := h₂
  refine ⟨z * w, isUnitPhase_mul hz hw, ?_⟩
  rw [he₁, he₂, smul_smul]

/-- Sequential congruence: the replaced circuit runs after the unchanged one. -/
theorem pre {n : Nat} {a b c : Circuit n} (h : PhaseEquivalent a b) :
    PhaseEquivalent (Circuit.seq c a) (Circuit.seq c b) := by
  obtain ⟨z, hz, he⟩ := h
  refine ⟨z, hz, ?_⟩
  show denote a * denote c = z • (denote b * denote c)
  rw [he, Matrix.smul_mul]

/-- Sequential congruence: the replaced circuit runs before the unchanged one. -/
theorem post {n : Nat} {a b c : Circuit n} (h : PhaseEquivalent a b) :
    PhaseEquivalent (Circuit.seq a c) (Circuit.seq b c) := by
  obtain ⟨z, hz, he⟩ := h
  refine ⟨z, hz, ?_⟩
  show denote c * denote a = z • (denote c * denote b)
  rw [he, Matrix.mul_smul]

theorem of_eqExact {n : Nat} {a b : Circuit n} (h : EqExact a b) : PhaseEquivalent a b :=
  ⟨1, isUnitPhase_one, by rw [h, one_smul]⟩

end PhaseEquivalent

/-- Phase equivalence is an equivalence relation on n-qubit circuits. -/
def phaseSetoid (n : Nat) : Setoid (Circuit n) where
  r := fun a b => PhaseEquivalent a b
  iseqv :=
    ⟨fun a => PhaseEquivalent.refl a, fun h => PhaseEquivalent.symm h,
     fun h₁ h₂ => PhaseEquivalent.trans h₁ h₂⟩

namespace EqExact

theorem refl {n : Nat} (a : Circuit n) : EqExact a a := rfl
theorem symm {n : Nat} {a b : Circuit n} (h : EqExact a b) : EqExact b a := Eq.symm h
theorem trans {n : Nat} {a b c : Circuit n} (h₁ : EqExact a b) (h₂ : EqExact b c) :
    EqExact a c := Eq.trans h₁ h₂

theorem pre {n : Nat} {a b c : Circuit n} (h : EqExact a b) :
    EqExact (Circuit.seq c a) (Circuit.seq c b) := by
  show denote a * denote c = denote b * denote c
  rw [h]

theorem post {n : Nat} {a b c : Circuit n} (h : EqExact a b) :
    EqExact (Circuit.seq a c) (Circuit.seq b c) := by
  show denote c * denote a = denote c * denote b
  rw [h]

end EqExact

end Quantum