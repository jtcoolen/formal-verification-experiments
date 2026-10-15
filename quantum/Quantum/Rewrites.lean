/-
The verified rewrite library.

A rule is a named pair of circuit patterns (given by instantiation functions from a list of
arguments), a decidable side condition, and a *proved* soundness theorem stating that every
instantiation whose side condition holds relates phase-equivalent circuits.

Every soundness theorem is derived from the matrix identities in Quantum/Gates.lean,
Quantum/Rotations.lean and Quantum/Embed.lean, i.e. from the independent matrix semantics of
Quantum/Semantics.lean.  Nothing in this file refers to the optimizer, to e-graphs, or to
extraction.

Rule identifiers are stable strings; Quantum/Certificates.lean looks rules up by them.
-/
import Quantum.Contexts
import Quantum.Semantics

namespace Quantum

open Classical

/-! ### Rule parameters -/

/-- Parameters of a rewrite rule: a qubit index, an exact angle, a gate, or a subcircuit. -/
inductive Arg (n : Nat) : Type where
  | q : Fin n -> Arg n
  | a : Angle -> Arg n
  | g : Gate n -> Arg n
  | c : Circuit n -> Arg n
deriving DecidableEq

namespace Arg

def q? : Arg n -> Option (Fin n)
  | q i => some i
  | _ => none

def a? : Arg n -> Option Angle
  | a t => some t
  | _ => none

def g? : Arg n -> Option (Gate n)
  | g k => some k
  | _ => none

def c? : Arg n -> Option (Circuit n)
  | c k => some k
  | _ => none

end Arg

/-- Do two gates act on disjoint sets of qubits? (decidable) -/
def Gate.disjoint (g₁ g₂ : Gate n) : Bool :=
  decide (∀ a ∈ g₁.qubits, ∀ b ∈ g₂.qubits, a ≠ b)

theorem Gate.disjoint_iff {g₁ g₂ : Gate n} :
    g₁.disjoint g₂ = true ↔ ∀ a ∈ g₁.qubits, ∀ b ∈ g₂.qubits, a ≠ b := by
  classical
  simp [Gate.disjoint]

theorem Gate.disjoint_symm {g₁ g₂ : Gate n} (h : g₁.disjoint g₂) : g₂.disjoint g₁ := by
  classical
  have h1 := Gate.disjoint_iff.mp h
  exact Gate.disjoint_iff.mpr (fun b hb a ha => Ne.symm (h1 a ha b hb))

/-! ### Rules -/

/-- A rewrite rule with a stable identifier, patterns over an argument list, a decidable side
condition, and a proof that every admissible instantiation is phase-preserving. -/
structure Rule (n : Nat) where
  id : String
  lhs : List (Arg n) -> Circuit n
  rhs : List (Arg n) -> Circuit n
  side : List (Arg n) -> Bool
  sound : ∀ args, side args = true -> PhaseEquivalent (lhs args) (rhs args)

/-- Build a rule from a shape-checking matcher.  If the matcher fails, both sides degenerate
to 'Circuit.one' and the side condition is false, so the rule simply does not apply. -/
def mkRule (name : String) {P : Type} (mt : List (Arg n) -> Option P)
    (lhs rhs : P -> Circuit n) (sound : ∀ p : P, PhaseEquivalent (lhs p) (rhs p)) :
    Rule n :=
  { id := name
    lhs := fun args => match mt args with | some p => lhs p | none => Circuit.one
    rhs := fun args => match mt args with | some p => rhs p | none => Circuit.one
    side := fun args => match mt args with | some _ => true | none => false
    sound := by
      intro args h
      rcases hmt : mt args with _ | p
      · simp_all
      · exact sound p }

/-- Helper: a circuit containing one single-qubit gate. -/
def gc (f : Fin n -> Gate n) (i : Fin n) : Circuit n := Circuit.gate (f i)

/-- Helper: sequential composition of two circuits. -/
def two (a b : Circuit n) : Circuit n := Circuit.seq a b

/-! ### Soundness of the individual rewrites -/

/-- Exact semantic equality of two circuits implies phase equivalence. -/
theorem phase_of_eq {n : Nat} {a b : Circuit n} (h : denote a = denote b) :
    PhaseEquivalent a b := ⟨1, isUnitPhase_one, by rw [h, one_smul]⟩

/-- A phase-scaled semantic identity implies phase equivalence. -/
theorem phase_of_smul {n : Nat} {a b : Circuit n} (z : ℂ) (hz : IsUnitPhase z)
    (h : denote a = z • denote b) : PhaseEquivalent a b := ⟨z, hz, h⟩

section Soundness

variable {n : Nat}

theorem rw_hh (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.h i)) (Circuit.gate (Gate.h i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 H2 i * embed1 H2 i = 1
  rw [embed1_mul, H2_mul_H2, embed1_one]

theorem rw_xx (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.x i)) (Circuit.gate (Gate.x i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 X2 i * embed1 X2 i = 1
  rw [embed1_mul, X2_mul_X2, embed1_one]

theorem rw_yy (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.y i)) (Circuit.gate (Gate.y i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 Y2 i * embed1 Y2 i = 1
  rw [embed1_mul, Y2_mul_Y2, embed1_one]

theorem rw_zz (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.z i)) (Circuit.gate (Gate.z i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 Z2 i * embed1 Z2 i = 1
  rw [embed1_mul, Z2_mul_Z2, embed1_one]

theorem rw_ss (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.s i)) (Circuit.gate (Gate.s i)))
      (Circuit.gate (Gate.z i)) := by
  refine phase_of_eq ?_
  show embed1 S2 i * embed1 S2 i = embed1 Z2 i
  rw [embed1_mul, S2_mul_S2]

theorem rw_tt (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.t i)) (Circuit.gate (Gate.t i)))
      (Circuit.gate (Gate.s i)) := by
  refine phase_of_eq ?_
  show embed1 T2 i * embed1 T2 i = embed1 S2 i
  rw [embed1_mul, T2_mul_T2]

theorem rw_sDag_s (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.sDag i)) (Circuit.gate (Gate.s i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 S2 i * embed1 S2Dag i = 1
  rw [embed1_mul, S2_mul_S2Dag, embed1_one]

theorem rw_s_sDag (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.s i)) (Circuit.gate (Gate.sDag i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 S2Dag i * embed1 S2 i = 1
  rw [embed1_mul, S2Dag_mul_S2, embed1_one]

theorem rw_tDag_t (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.tDag i)) (Circuit.gate (Gate.t i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 T2 i * embed1 T2Dag i = 1
  rw [embed1_mul, T2_mul_T2Dag, embed1_one]

theorem rw_t_tDag (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.t i)) (Circuit.gate (Gate.tDag i)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed1 T2Dag i * embed1 T2 i = 1
  rw [embed1_mul, T2Dag_mul_T2, embed1_one]

theorem rw_hXH (i : Fin n) :
    PhaseEquivalent
      (Circuit.seq (Circuit.seq (Circuit.gate (Gate.h i)) (Circuit.gate (Gate.x i)))
        (Circuit.gate (Gate.h i))) (Circuit.gate (Gate.z i)) := by
  refine phase_of_eq ?_
  show embed1 H2 i * (embed1 X2 i * embed1 H2 i) = embed1 Z2 i
  rw [← Matrix.mul_assoc, embed1_mul, embed1_mul, H2_mul_X2_mul_H2]

theorem rw_hZH (i : Fin n) :
    PhaseEquivalent
      (Circuit.seq (Circuit.seq (Circuit.gate (Gate.h i)) (Circuit.gate (Gate.z i)))
        (Circuit.gate (Gate.h i))) (Circuit.gate (Gate.x i)) := by
  refine phase_of_eq ?_
  show embed1 H2 i * (embed1 Z2 i * embed1 H2 i) = embed1 X2 i
  rw [← Matrix.mul_assoc, embed1_mul, embed1_mul, H2_mul_Z2_mul_H2]

/-- If a = (-1) • b then b = (-1) • a: anticommutation is symmetric. -/
theorem neg_smul_phase {α : Type} [AddCommGroup α] [Module ℂ α] {a b : α}
    (h : a = (-1 : ℂ) • b) : b = (-1 : ℂ) • a := by
  have : ((-1 : ℂ) • (-1 : ℂ) • b) = b := by
    rw [smul_smul]
    norm_num
  rw [← h] at this
  exact this.symm

/-- Pauli X and Z anticommute: the two products differ by the global phase -1. -/
theorem rw_xz (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.x i)) (Circuit.gate (Gate.z i)))
      (Circuit.seq (Circuit.gate (Gate.z i)) (Circuit.gate (Gate.x i))) := by
  refine phase_of_smul (-1) isUnitPhase_neg_one ?_
  show embed1 Z2 i * embed1 X2 i = (-1 : ℂ) • (embed1 X2 i * embed1 Z2 i)
  rw [embed1_mul, embed1_mul, neg_smul_phase X2_mul_Z2_phase, embed1_smul]

theorem rw_xy (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.x i)) (Circuit.gate (Gate.y i)))
      (Circuit.seq (Circuit.gate (Gate.y i)) (Circuit.gate (Gate.x i))) := by
  refine phase_of_smul (-1) isUnitPhase_neg_one ?_
  show embed1 Y2 i * embed1 X2 i = (-1 : ℂ) • (embed1 X2 i * embed1 Y2 i)
  rw [embed1_mul, embed1_mul, neg_smul_phase X2_mul_Y2_phase, embed1_smul]

theorem rw_yz (i : Fin n) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.y i)) (Circuit.gate (Gate.z i)))
      (Circuit.seq (Circuit.gate (Gate.z i)) (Circuit.gate (Gate.y i))) := by
  refine phase_of_smul (-1) isUnitPhase_neg_one ?_
  show embed1 Z2 i * embed1 Y2 i = (-1 : ℂ) • (embed1 Y2 i * embed1 Z2 i)
  rw [embed1_mul, embed1_mul, neg_smul_phase Y2_mul_Z2_phase, embed1_smul]

theorem rw_rz_add (i : Fin n) (s t : Angle) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.rz i s)) (Circuit.gate (Gate.rz i t)))
      (Circuit.gate (Gate.rz i (s + t))) := by
  refine phase_of_eq ?_
  show embed1 (Rz2 (Angle.val t)) i * embed1 (Rz2 (Angle.val s)) i
      = embed1 (Rz2 (Angle.val (s + t))) i
  rw [embed1_mul, Rz2_mul, Angle.val_add, add_comm]

theorem rw_rz_zero (i : Fin n) :
    PhaseEquivalent (Circuit.gate (Gate.rz i 0)) Circuit.one := by
  refine phase_of_eq ?_
  show embed1 (Rz2 (Angle.val 0)) i = 1
  rw [Angle.val_zero, Rz2_zero, embed1_one]

theorem rw_rx_add (i : Fin n) (s t : Angle) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.rx i s)) (Circuit.gate (Gate.rx i t)))
      (Circuit.gate (Gate.rx i (s + t))) := by
  refine phase_of_eq ?_
  show embed1 (Rx2 (Angle.val t)) i * embed1 (Rx2 (Angle.val s)) i
      = embed1 (Rx2 (Angle.val (s + t))) i
  rw [embed1_mul, Rx2_mul, Angle.val_add, add_comm]

theorem rw_rx_zero (i : Fin n) :
    PhaseEquivalent (Circuit.gate (Gate.rx i 0)) Circuit.one := by
  refine phase_of_eq ?_
  show embed1 (Rx2 (Angle.val 0)) i = 1
  rw [Angle.val_zero, Rx2_zero, embed1_one]

theorem rw_ry_add (i : Fin n) (s t : Angle) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.ry i s)) (Circuit.gate (Gate.ry i t)))
      (Circuit.gate (Gate.ry i (s + t))) := by
  refine phase_of_eq ?_
  show embed1 (Ry2 (Angle.val t)) i * embed1 (Ry2 (Angle.val s)) i
      = embed1 (Ry2 (Angle.val (s + t))) i
  rw [embed1_mul, Ry2_mul, Angle.val_add, add_comm]

theorem rw_ry_zero (i : Fin n) :
    PhaseEquivalent (Circuit.gate (Gate.ry i 0)) Circuit.one := by
  refine phase_of_eq ?_
  show embed1 (Ry2 (Angle.val 0)) i = 1
  rw [Angle.val_zero, Ry2_zero, embed1_one]

/-- Rz(pi) equals Z up to the global phase -i.  (Rz(pi) is NOT phase-equivalent to S: see
Quantum.Rotations.Rz2_pi_phase_not.) -/
theorem rw_rz_pi_z (i : Fin n) :
    PhaseEquivalent (Circuit.gate (Gate.rz i Angle.pi)) (Circuit.gate (Gate.z i)) := by
  refine phase_of_smul (-Complex.I) ?_ ?_
  · show Complex.normSq (-Complex.I) = 1
    norm_num [Complex.normSq_apply, Complex.I_re, Complex.I_im]
  · show embed1 (Rz2 (Angle.val Angle.pi)) i = (-Complex.I) • embed1 Z2 i
    rw [Angle.val_pi, Rz2_pi_Z2, embed1_smul]

/-- Rz(pi/2) equals S up to the global phase exp(-i pi/4). -/
theorem rw_rz_halfPi_s (i : Fin n) :
    PhaseEquivalent (Circuit.gate (Gate.rz i (Angle.piMul (1 / 2)))) (Circuit.gate (Gate.s i)) := by
  refine phase_of_smul (Complex.exp (-(Complex.I * (Real.pi / 4)))) ?_ ?_
  · have h : -(Complex.I * (Real.pi / 4)) = Complex.I * ((-(Real.pi / 4) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h]
    exact isUnitPhase_exp_I (-(Real.pi / 4))
  · show embed1 (Rz2 (Angle.val (Angle.piMul (1 / 2)))) i
        = Complex.exp (-(Complex.I * (Real.pi / 4))) • embed1 S2 i
    rw [Angle.val_piMul, show ((1 / 2 : ℚ) : ℝ) * Real.pi = Real.pi / 2 by ring,
      Rz2_halfPi_S2, embed1_smul]

/-- Rz(2 pi) is the identity up to the global phase -1.  This is valid *uncontrolled*; the
controlled version CRz(2 pi) is NOT equivalent to the identity
(see Quantum/ControlPhase.lean). -/
theorem rw_rz_twoPi (i : Fin n) :
    PhaseEquivalent (Circuit.gate (Gate.rz i Angle.twoPi)) Circuit.one := by
  refine phase_of_smul (-1) isUnitPhase_neg_one ?_
  show embed1 (Rz2 (Angle.val Angle.twoPi)) i = (-1 : ℂ) • (1 : Operator n)
  rw [Angle.val_twoPi, Rz2_twoPi, embed1_smul, embed1_one]

theorem rw_cxcx {i j : Fin n} (h : i ≠ j) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.cx i j h)) (Circuit.gate (Gate.cx i j h)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed2 CNOT4 i j * embed2 CNOT4 i j = 1
  rw [embed2_mul (hij := h), CNOT4_mul_CNOT4, embed2_one h]

theorem rw_czcz {i j : Fin n} (h : i ≠ j) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.cz i j h)) (Circuit.gate (Gate.cz i j h)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed2 CZ4 i j * embed2 CZ4 i j = 1
  rw [embed2_mul (hij := h), CZ4_mul_CZ4, embed2_one h]

theorem rw_swapswap {i j : Fin n} (h : i ≠ j) :
    PhaseEquivalent
      (Circuit.seq (Circuit.gate (Gate.swap i j h)) (Circuit.gate (Gate.swap i j h)))
      Circuit.one := by
  refine phase_of_eq ?_
  show embed2 SWAP4 i j * embed2 SWAP4 i j = 1
  rw [embed2_mul (hij := h), SWAP4_mul_SWAP4, embed2_one h]

theorem rw_cp_add {i j : Fin n} (h : i ≠ j) (s t : Angle) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.cp i j h s))
      (Circuit.gate (Gate.cp i j h t))) (Circuit.gate (Gate.cp i j h (s + t))) := by
  refine phase_of_eq ?_
  show embed2 (CP4 (Angle.val t)) i j * embed2 (CP4 (Angle.val s)) i j
      = embed2 (CP4 (Angle.val (s + t))) i j
  rw [embed2_mul (hij := h), CP4_mul, Angle.val_add, add_comm]

theorem rw_cp_zero {i j : Fin n} (h : i ≠ j) :
    PhaseEquivalent (Circuit.gate (Gate.cp i j h 0)) Circuit.one := by
  refine phase_of_eq ?_
  show embed2 (CP4 (Angle.val 0)) i j = 1
  rw [Angle.val_zero, CP4_zero, embed2_one h]

theorem rw_crz_zero {i j : Fin n} (h : i ≠ j) :
    PhaseEquivalent (Circuit.gate (Gate.crz i j h 0)) Circuit.one := by
  refine phase_of_eq ?_
  show embed2 (CRz4 (Angle.val 0)) i j = 1
  rw [Angle.val_zero, CRz4_zero, embed2_one h]

theorem rw_crz_add {i j : Fin n} (h : i ≠ j) (s t : Angle) :
    PhaseEquivalent (Circuit.seq (Circuit.gate (Gate.crz i j h s))
      (Circuit.gate (Gate.crz i j h t))) (Circuit.gate (Gate.crz i j h (s + t))) := by
  refine phase_of_eq ?_
  show embed2 (CRz4 (Angle.val t)) i j * embed2 (CRz4 (Angle.val s)) i j
      = embed2 (CRz4 (Angle.val (s + t))) i j
  rw [embed2_mul (hij := h), CRz4_mul, Angle.val_add, add_comm]

end Soundness

/-! ### Disjoint-support commutation -/

/-- The 2x2 matrix of a single-qubit gate (arbitrary for two-qubit gates). -/
noncomputable def Gate.mat1 : Gate n -> Matrix Bool Bool ℂ
  | Gate.h _ => H2
  | Gate.x _ => X2
  | Gate.y _ => Y2
  | Gate.z _ => Z2
  | Gate.s _ => S2
  | Gate.t _ => T2
  | Gate.sDag _ => S2Dag
  | Gate.tDag _ => T2Dag
  | Gate.rz _ a => Rz2 (Angle.val a)
  | Gate.rx _ a => Rx2 (Angle.val a)
  | Gate.ry _ a => Ry2 (Angle.val a)
  | _ => 1

/-- The 4x4 matrix of a two-qubit gate (arbitrary for single-qubit gates). -/
noncomputable def Gate.mat2 : Gate n -> Matrix (Bool × Bool) (Bool × Bool) ℂ
  | Gate.cx _ _ _ => CNOT4
  | Gate.cz _ _ _ => CZ4
  | Gate.swap _ _ _ => SWAP4
  | Gate.crz _ _ _ a => CRz4 (Angle.val a)
  | Gate.cp _ _ _ a => CP4 (Angle.val a)
  | _ => 1

theorem denoteGate_embed1 {g : Gate n} {i : Fin n} (h : g.index1? = some i) :
    denoteGate g = embed1 g.mat1 i := by
  cases g <;> simp_all [Gate.index1?, Gate.mat1, denoteGate]

theorem denoteGate_embed2 {g : Gate n} {i j : Fin n} (h : g.index2? = some (i, j)) :
    denoteGate g = embed2 g.mat2 i j := by
  cases g <;> simp_all [Gate.index2?, Gate.mat2, denoteGate]

theorem Gate.qubits_of_index1? {g : Gate n} {i : Fin n} (h : g.index1? = some i) :
    g.qubits = [i] := by
  cases g <;> simp_all [Gate.index1?, Gate.qubits]

theorem Gate.qubits_of_index2? {g : Gate n} {i j : Fin n} (h : g.index2? = some (i, j)) :
    g.qubits = [i, j] := by
  cases g <;> simp_all [Gate.index2?, Gate.qubits]

theorem Gate.ne_of_index2? {g : Gate n} {i j : Fin n} (h : g.index2? = some (i, j)) :
    i ≠ j := by
  have key : ∀ (a b : Fin n), (a, b) = (i, j) -> a ≠ b -> i ≠ j := by
    intro a b hab hne
    obtain ⟨rfl, rfl⟩ := hab
    exact hne
  cases g with
  | h a => exact absurd h (by simp [Gate.index2?])
  | x a => exact absurd h (by simp [Gate.index2?])
  | y a => exact absurd h (by simp [Gate.index2?])
  | z a => exact absurd h (by simp [Gate.index2?])
  | s a => exact absurd h (by simp [Gate.index2?])
  | t a => exact absurd h (by simp [Gate.index2?])
  | sDag a => exact absurd h (by simp [Gate.index2?])
  | tDag a => exact absurd h (by simp [Gate.index2?])
  | rz a _ => exact absurd h (by simp [Gate.index2?])
  | rx a _ => exact absurd h (by simp [Gate.index2?])
  | ry a _ => exact absurd h (by simp [Gate.index2?])
  | cx a b hab => exact key a b (by simpa [Gate.index2?] using h) hab
  | cz a b hab => exact key a b (by simpa [Gate.index2?] using h) hab
  | swap a b hab => exact key a b (by simpa [Gate.index2?] using h) hab
  | crz a b hab _ => exact key a b (by simpa [Gate.index2?] using h) hab
  | cp a b hab _ => exact key a b (by simpa [Gate.index2?] using h) hab

/-- Every gate is either single-qubit or two-qubit. -/
theorem Gate.arity (g : Gate n) :
    (∃ i, g.index1? = some i) ∨ (∃ i j, g.index2? = some (i, j)) := by
  cases g
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · right; exact ⟨_, _, rfl⟩
  · right; exact ⟨_, _, rfl⟩
  · right; exact ⟨_, _, rfl⟩
  · right; exact ⟨_, _, rfl⟩
  · right; exact ⟨_, _, rfl⟩

/-- Gates acting on disjoint sets of qubits commute (exactly, not merely up to phase). -/
theorem rw_disjoint {g₁ g₂ : Gate n} (h : g₁.disjoint g₂ = true) :
    PhaseEquivalent (Circuit.seq (Circuit.gate g₁) (Circuit.gate g₂))
      (Circuit.seq (Circuit.gate g₂) (Circuit.gate g₁)) :=
  PhaseEquivalent.of_eqExact (by
    classical
    show denoteGate g₂ * denoteGate g₁ = denoteGate g₁ * denoteGate g₂
    have hd : ∀ a ∈ g₁.qubits, ∀ b ∈ g₂.qubits, a ≠ b := Gate.disjoint_iff.mp h
    rcases Gate.arity g₁ with ⟨i, hi⟩ | ⟨i, j, hij⟩
    · rcases Gate.arity g₂ with ⟨k, hk⟩ | ⟨k, l, hkl⟩
      · have hik : i ≠ k := hd i (by rw [Gate.qubits_of_index1? hi]; simp) k
            (by rw [Gate.qubits_of_index1? hk]; simp)
        rw [denoteGate_embed1 hi, denoteGate_embed1 hk, embed1_embed1_comm hik]
      · have h1 : i ≠ k := hd i (by rw [Gate.qubits_of_index1? hi]; simp) k
            (by rw [Gate.qubits_of_index2? hkl]; simp)
        have h2 : i ≠ l := hd i (by rw [Gate.qubits_of_index1? hi]; simp) l
            (by rw [Gate.qubits_of_index2? hkl]; simp)
        have h3 : k ≠ l := Gate.ne_of_index2? hkl
        rw [denoteGate_embed1 hi, denoteGate_embed2 hkl, embed1_embed2_comm h1 h2 h3]
    · rcases Gate.arity g₂ with ⟨k, hk⟩ | ⟨k, l, hkl⟩
      · have h1 : i ≠ k := hd i (by rw [Gate.qubits_of_index2? hij]; simp) k
            (by rw [Gate.qubits_of_index1? hk]; simp)
        have h2 : j ≠ k := hd j (by rw [Gate.qubits_of_index2? hij]; simp) k
            (by rw [Gate.qubits_of_index1? hk]; simp)
        have h3 : i ≠ j := Gate.ne_of_index2? hij
        rw [denoteGate_embed2 hij, denoteGate_embed1 hk, embed2_embed1_comm h3 h1 h2]
      · have h1 : i ≠ k := hd i (by rw [Gate.qubits_of_index2? hij]; simp) k
            (by rw [Gate.qubits_of_index2? hkl]; simp)
        have h2 : i ≠ l := hd i (by rw [Gate.qubits_of_index2? hij]; simp) l
            (by rw [Gate.qubits_of_index2? hkl]; simp)
        have h3 : j ≠ k := hd j (by rw [Gate.qubits_of_index2? hij]; simp) k
            (by rw [Gate.qubits_of_index2? hkl]; simp)
        have h4 : j ≠ l := hd j (by rw [Gate.qubits_of_index2? hij]; simp) l
            (by rw [Gate.qubits_of_index2? hkl]; simp)
        rw [denoteGate_embed2 hij, denoteGate_embed2 hkl, embed2_embed2_comm h1 h2 h3 h4])

/-- A circuit followed by its uncomputation is the identity, *exactly*.  This is the
uncomputation / dead-code law used by reversible-circuit optimizers: a compute block and the
matching uncompute block annihilate. -/
theorem rw_uncompute {n : Nat} (c : Circuit n) :
    PhaseEquivalent (Circuit.seq (Circuit.inv c) c) Circuit.one := by
  refine phase_of_eq ?_
  show denote c * denote (Circuit.inv c) = 1
  exact denote_mul_inv c

/-- The same annihilation in the other order. -/
theorem rw_uncompute2 {n : Nat} (c : Circuit n) :
    PhaseEquivalent (Circuit.seq c (Circuit.inv c)) Circuit.one := by
  refine phase_of_eq ?_
  show denote (Circuit.inv c) * denote c = 1
  exact denote_inv_mul c

/-! ### Matchers for rule arguments -/

def oneQ : List (Arg n) -> Option (Fin n)
  | [Arg.q i] => some i
  | _ => none

def twoQne : List (Arg n) -> Option { p : Fin n × Fin n // p.1 ≠ p.2 }
  | [Arg.q i, Arg.q j] => if h : i ≠ j then some ⟨(i, j), h⟩ else none
  | _ => none

def qAngAng : List (Arg n) -> Option (Fin n × (Angle × Angle))
  | [Arg.q i, Arg.a s, Arg.a t] => some (i, s, t)
  | _ => none

def twoQAngAng : List (Arg n) ->
    Option { p : Fin n × (Fin n × (Angle × Angle)) // p.1 ≠ p.2.1 }
  | [Arg.q i, Arg.q j, Arg.a s, Arg.a t] => if h : i ≠ j then some ⟨(i, j, s, t), h⟩ else none
  | _ => none

def twoGatesDisjoint : List (Arg n) -> Option { p : Gate n × Gate n // p.1.disjoint p.2 = true }
  | [Arg.g g₁, Arg.g g₂] => if h : g₁.disjoint g₂ then some ⟨(g₁, g₂), h⟩ else none
  | _ => none

def threeCirc : List (Arg n) -> Option (Circuit n × Circuit n × Circuit n)
  | [Arg.c a, Arg.c b, Arg.c c] => some (a, b, c)
  | _ => none

def oneCircAfterId : List (Arg n) -> Option (Circuit n)
  | [Arg.c x, Arg.c c] => if x = Circuit.one then some c else none
  | _ => none

def oneCircBeforeId : List (Arg n) -> Option (Circuit n)
  | [Arg.c c, Arg.c x] => if x = Circuit.one then some c else none
  | _ => none

/-! ### Rule constructors -/

/-- Two identical self-inverse single-qubit gates cancel. -/
def ruleSelfInv (f : Fin n -> Gate n) (name : String)
    (h : ∀ i, PhaseEquivalent (Circuit.seq (gc f i) (gc f i)) Circuit.one) : Rule n :=
  mkRule (n := n) name oneQ (fun i => Circuit.seq (gc f i) (gc f i)) (fun _ => Circuit.one) h

/-- A gate followed by its inverse cancels. -/
def ruleInvPair (f g : Fin n -> Gate n) (name : String)
    (h : ∀ i, PhaseEquivalent (Circuit.seq (gc f i) (gc g i)) Circuit.one) : Rule n :=
  mkRule (n := n) name oneQ (fun i => Circuit.seq (gc f i) (gc g i)) (fun _ => Circuit.one) h

/-- Two copies of a gate replace by one copy of another gate. -/
def ruleDouble (f g : Fin n -> Gate n) (name : String)
    (h : ∀ i, PhaseEquivalent (Circuit.seq (gc f i) (gc f i)) (gc g i)) : Rule n :=
  mkRule (n := n) name oneQ (fun i => Circuit.seq (gc f i) (gc f i)) (fun i => gc g i) h

/-- Two gates on the same qubit that anticommute: swap them (global phase -1). -/
def rulePhaseComm (f g : Fin n -> Gate n) (name : String)
    (h : ∀ i, PhaseEquivalent (Circuit.seq (gc f i) (gc g i)) (Circuit.seq (gc g i) (gc f i))) :
    Rule n :=
  mkRule (n := n) name oneQ (fun i => Circuit.seq (gc f i) (gc g i))
    (fun i => Circuit.seq (gc g i) (gc f i)) h

/-- H conjugation: H ; F ; H = G. -/
def ruleHConj (f g : Fin n -> Gate n) (name : String)
    (h : ∀ i, PhaseEquivalent (Circuit.seq (Circuit.seq (gc Gate.h i) (gc f i)) (gc Gate.h i))
      (gc g i)) : Rule n :=
  mkRule (n := n) name oneQ
    (fun i => Circuit.seq (Circuit.seq (gc Gate.h i) (gc f i)) (gc Gate.h i)) (fun i => gc g i) h

/-- Adding two rotation angles on the same qubit. -/
def ruleAddRot (f : (i : Fin n) -> Angle -> Gate n) (name : String)
    (h : ∀ i s t, PhaseEquivalent (Circuit.seq (Circuit.gate (f i s)) (Circuit.gate (f i t)))
      (Circuit.gate (f i (s + t)))) : Rule n :=
  mkRule (n := n) name qAngAng
    (fun p => Circuit.seq (Circuit.gate (f p.1 p.2.1)) (Circuit.gate (f p.1 p.2.2)))
    (fun p => Circuit.gate (f p.1 (p.2.1 + p.2.2))) (fun p => h p.1 p.2.1 p.2.2)

/-- A rotation by the zero angle disappears. -/
def ruleRotZero (f : (i : Fin n) -> Angle -> Gate n) (name : String)
    (h : ∀ i, PhaseEquivalent (Circuit.gate (f i 0)) Circuit.one) : Rule n :=
  mkRule (n := n) name oneQ (fun i => Circuit.gate (f i 0)) (fun _ => Circuit.one) h

/-- Two identical self-inverse two-qubit gates cancel. -/
def ruleSelfInv2 (f : (a b : Fin n) -> a ≠ b -> Gate n) (name : String)
    (h : ∀ {i j : Fin n} (hij : i ≠ j),
      PhaseEquivalent (Circuit.seq (Circuit.gate (f i j hij)) (Circuit.gate (f i j hij)))
        Circuit.one) : Rule n :=
  mkRule (n := n) name twoQne
    (fun p => Circuit.seq (Circuit.gate (f p.val.1 p.val.2 p.property))
      (Circuit.gate (f p.val.1 p.val.2 p.property)))
    (fun _ => Circuit.one) (fun p => h (hij := p.property))

/-- A controlled rotation by the zero angle disappears. -/
def ruleCrzZero (n : Nat) : Rule n :=
  mkRule (n := n) "crz_zero" twoQne
    (fun p => Circuit.gate (Gate.crz p.val.1 p.val.2 p.property 0)) (fun _ => Circuit.one)
    (fun p => rw_crz_zero (h := p.property))

/-- A controlled phase by the zero angle disappears. -/
def ruleCpZero (n : Nat) : Rule n :=
  mkRule (n := n) "cp_zero" twoQne
    (fun p => Circuit.gate (Gate.cp p.val.1 p.val.2 p.property 0)) (fun _ => Circuit.one)
    (fun p => rw_cp_zero (h := p.property))

/-- Adding two controlled-rotation angles. -/
def ruleAddRot2 (f : (a b : Fin n) -> a ≠ b -> Angle -> Gate n) (name : String)
    (h : ∀ {i j : Fin n} (hij : i ≠ j) (s t : Angle),
      PhaseEquivalent (Circuit.seq (Circuit.gate (f i j hij s)) (Circuit.gate (f i j hij t)))
        (Circuit.gate (f i j hij (s + t)))) : Rule n :=
  mkRule (n := n) name twoQAngAng
    (fun p => Circuit.seq (Circuit.gate (f p.val.1 p.val.2.1 p.property p.val.2.2.1))
      (Circuit.gate (f p.val.1 p.val.2.1 p.property p.val.2.2.2)))
    (fun p => Circuit.gate (f p.val.1 p.val.2.1 p.property (p.val.2.2.1 + p.val.2.2.2)))
    (fun p => h (hij := p.property) p.val.2.2.1 p.val.2.2.2)

/-! ### Structural rules -/

theorem rw_idL {n : Nat} (c : Circuit n) :
    PhaseEquivalent (Circuit.seq Circuit.one c) c := by
  refine PhaseEquivalent.of_eqExact ?_
  show denote c * (1 : Operator n) = denote c
  rw [Matrix.mul_one]

theorem rw_idR {n : Nat} (c : Circuit n) :
    PhaseEquivalent (Circuit.seq c Circuit.one) c := by
  refine PhaseEquivalent.of_eqExact ?_
  show (1 : Operator n) * denote c = denote c
  rw [Matrix.one_mul]

theorem rw_assoc {n : Nat} (a b c : Circuit n) :
    PhaseEquivalent (Circuit.seq (Circuit.seq a b) c) (Circuit.seq a (Circuit.seq b c)) := by
  refine PhaseEquivalent.of_eqExact ?_
  show denote c * (denote b * denote a) = (denote c * denote b) * denote a
  rw [Matrix.mul_assoc]

/-- Drop a leading identity. -/
def ruleIdL (n : Nat) : Rule n :=
  mkRule (n := n) "idL" oneCircAfterId (fun c => Circuit.seq Circuit.one c) (fun c => c)
    (fun c => rw_idL c)

/-- Drop a trailing identity. -/
def ruleIdR (n : Nat) : Rule n :=
  mkRule (n := n) "idR" oneCircBeforeId (fun c => Circuit.seq c Circuit.one) (fun c => c)
    (fun c => rw_idR c)

/-- Associativity of sequential composition (exact semantic equality). -/
def ruleAssoc (n : Nat) : Rule n :=
  mkRule (n := n) "assoc" threeCirc
    (fun p => Circuit.seq (Circuit.seq p.1 p.2.1) p.2.2)
    (fun p => Circuit.seq p.1 (Circuit.seq p.2.1 p.2.2))
    (fun p => rw_assoc p.1 p.2.1 p.2.2)

/-! ### The rule library -/

/-- Matches a pair of circuits that are mutual inverses: `seq (inv c) c`. -/
def circInvPair : List (Arg n) -> Option (Circuit n)
  | [Arg.c a, Arg.c b] => if a = Circuit.inv b then some b else none
  | _ => none

/-- Matches a pair of circuits that are mutual inverses: `seq c (inv c)`. -/
def circPairInv : List (Arg n) -> Option (Circuit n)
  | [Arg.c a, Arg.c b] => if b = Circuit.inv a then some a else none
  | _ => none

/-- Circuit-level uncomputation: `inv c ; c = I` (exactly). -/
def ruleUncompute (n : Nat) : Rule n :=
  mkRule (n := n) "uncompute" circInvPair (fun c => Circuit.seq (Circuit.inv c) c)
    (fun _ => Circuit.one) (fun c => rw_uncompute c)

/-- Circuit-level uncomputation the other way round: `c ; inv c = I` (exactly). -/
def ruleUncompute2 (n : Nat) : Rule n :=
  mkRule (n := n) "uncompute2" circPairInv (fun c => Circuit.seq c (Circuit.inv c))
    (fun _ => Circuit.one) (fun c => rw_uncompute2 c)

/-- The complete rewrite library for n-qubit circuits. -/
def rules (n : Nat) : List (Rule n) :=
  [ ruleIdL n, ruleIdR n, ruleAssoc n, ruleUncompute n, ruleUncompute2 n,
    ruleSelfInv Gate.h "hh" rw_hh,
    ruleSelfInv Gate.x "xx" rw_xx,
    ruleSelfInv Gate.y "yy" rw_yy,
    ruleSelfInv Gate.z "zz" rw_zz,
    ruleDouble Gate.s Gate.z "ss" rw_ss,
    ruleDouble Gate.t Gate.s "tt" rw_tt,
    ruleInvPair Gate.sDag Gate.s "sdag_s" rw_sDag_s,
    ruleInvPair Gate.s Gate.sDag "s_sdag" rw_s_sDag,
    ruleInvPair Gate.tDag Gate.t "tdag_t" rw_tDag_t,
    ruleInvPair Gate.t Gate.tDag "t_tdag" rw_t_tDag,
    ruleHConj Gate.x Gate.z "hXH" rw_hXH,
    ruleHConj Gate.z Gate.x "hZH" rw_hZH,
    rulePhaseComm Gate.x Gate.z "xz" rw_xz,
    rulePhaseComm Gate.x Gate.y "xy" rw_xy,
    rulePhaseComm Gate.y Gate.z "yz" rw_yz,
    ruleAddRot Gate.rz "rz_add" rw_rz_add,
    ruleRotZero Gate.rz "rz_zero" rw_rz_zero,
    ruleAddRot Gate.rx "rx_add" rw_rx_add,
    ruleRotZero Gate.rx "rx_zero" rw_rx_zero,
    ruleAddRot Gate.ry "ry_add" rw_ry_add,
    ruleRotZero Gate.ry "ry_zero" rw_ry_zero,
    ruleSelfInv2 Gate.cx "cxcx" rw_cxcx,
    ruleSelfInv2 Gate.cz "czcz" rw_czcz,
    ruleSelfInv2 Gate.swap "swapswap" rw_swapswap,
    ruleAddRot2 (fun i j h => Gate.crz i j h) "crz_add" rw_crz_add,
    ruleCrzZero n,
    ruleAddRot2 (fun i j h => Gate.cp i j h) "cp_add" rw_cp_add,
    ruleCpZero n,
    mkRule (n := n) "rz_pi_z" oneQ (fun i => gc (fun k => Gate.rz k Angle.pi) i)
      (fun i => gc Gate.z i) (fun i => rw_rz_pi_z i),
    mkRule (n := n) "rz_halfPi_s" oneQ
      (fun i => gc (fun k => Gate.rz k (Angle.piMul (1 / 2))) i)
      (fun i => gc Gate.s i) (fun i => rw_rz_halfPi_s i),
    mkRule (n := n) "rz_twoPi_one" oneQ (fun i => gc (fun k => Gate.rz k Angle.twoPi) i)
      (fun _ => Circuit.one) (fun i => rw_rz_twoPi i),
    mkRule (n := n) "disjoint" twoGatesDisjoint
      (fun p => Circuit.seq (Circuit.gate p.val.1) (Circuit.gate p.val.2))
      (fun p => Circuit.seq (Circuit.gate p.val.2) (Circuit.gate p.val.1))
      (fun p => rw_disjoint p.property) ]

/-- Look up a rule by its stable identifier. -/
def findRule (n : Nat) (name : String) : Option (Rule n) :=
  (rules n).find? fun r => r.id == name

theorem findRule_sound {n : Nat} (r : Rule n) (name : String)
    (h : findRule n name = some r) :
    ∀ args, r.side args = true -> PhaseEquivalent (r.lhs args) (r.rhs args) := r.sound

end Quantum