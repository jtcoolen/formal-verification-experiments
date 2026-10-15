/-
Denotational semantics of circuits: denote : Circuit n -> Operator n, unitarity of every
circuit, and the semantics of the normal form.

Composition convention: 'seq a b' executes a first and then b, so 'denote (seq a b) =
denote b * denote a'.
-/
import Quantum.Embed
import Quantum.Rotations

namespace Quantum

open Classical

/-! ### Gate and circuit denotation -/

/-- The operator denoted by a primitive gate: its gate matrix embedded at the gate's qubits. -/
noncomputable def denoteGate {n : Nat} : Gate n -> Operator n
  | Gate.h i => embed1 H2 i
  | Gate.x i => embed1 X2 i
  | Gate.y i => embed1 Y2 i
  | Gate.z i => embed1 Z2 i
  | Gate.s i => embed1 S2 i
  | Gate.t i => embed1 T2 i
  | Gate.sDag i => embed1 S2Dag i
  | Gate.tDag i => embed1 T2Dag i
  | Gate.rz i a => embed1 (Rz2 (Angle.val a)) i
  | Gate.rx i a => embed1 (Rx2 (Angle.val a)) i
  | Gate.ry i a => embed1 (Ry2 (Angle.val a)) i
  | Gate.cx i j _ => embed2 CNOT4 i j
  | Gate.cz i j _ => embed2 CZ4 i j
  | Gate.swap i j _ => embed2 SWAP4 i j
  | Gate.crz i j _ a => embed2 (CRz4 (Angle.val a)) i j

/-- The operator denoted by a circuit. -/
noncomputable def denote {n : Nat} : Circuit n -> Operator n
  | Circuit.one => 1
  | Circuit.seq a b => denote b * denote a
  | Circuit.gate g => denoteGate g

@[simp] theorem denoteGate_h {n : Nat} (i : Fin n) : denoteGate (Gate.h i) = embed1 H2 i := rfl
@[simp] theorem denoteGate_x {n : Nat} (i : Fin n) : denoteGate (Gate.x i) = embed1 X2 i := rfl
@[simp] theorem denoteGate_y {n : Nat} (i : Fin n) : denoteGate (Gate.y i) = embed1 Y2 i := rfl
@[simp] theorem denoteGate_z {n : Nat} (i : Fin n) : denoteGate (Gate.z i) = embed1 Z2 i := rfl
@[simp] theorem denoteGate_s {n : Nat} (i : Fin n) : denoteGate (Gate.s i) = embed1 S2 i := rfl
@[simp] theorem denoteGate_t {n : Nat} (i : Fin n) : denoteGate (Gate.t i) = embed1 T2 i := rfl
@[simp] theorem denoteGate_sDag {n : Nat} (i : Fin n) : denoteGate (Gate.sDag i) = embed1 S2Dag i := rfl
@[simp] theorem denoteGate_tDag {n : Nat} (i : Fin n) : denoteGate (Gate.tDag i) = embed1 T2Dag i := rfl
@[simp] theorem denoteGate_rz {n : Nat} (i : Fin n) (a : Angle) :
    denoteGate (Gate.rz i a) = embed1 (Rz2 (Angle.val a)) i := rfl
@[simp] theorem denoteGate_rx {n : Nat} (i : Fin n) (a : Angle) :
    denoteGate (Gate.rx i a) = embed1 (Rx2 (Angle.val a)) i := rfl
@[simp] theorem denoteGate_ry {n : Nat} (i : Fin n) (a : Angle) :
    denoteGate (Gate.ry i a) = embed1 (Ry2 (Angle.val a)) i := rfl
@[simp] theorem denoteGate_cx {n : Nat} (i j : Fin n) (h : i ≠ j) :
    denoteGate (Gate.cx i j h) = embed2 CNOT4 i j := rfl
@[simp] theorem denoteGate_cz {n : Nat} (i j : Fin n) (h : i ≠ j) :
    denoteGate (Gate.cz i j h) = embed2 CZ4 i j := rfl
@[simp] theorem denoteGate_swap {n : Nat} (i j : Fin n) (h : i ≠ j) :
    denoteGate (Gate.swap i j h) = embed2 SWAP4 i j := rfl
@[simp] theorem denoteGate_crz {n : Nat} (i j : Fin n) (h : i ≠ j) (a : Angle) :
    denoteGate (Gate.crz i j h a) = embed2 (CRz4 (Angle.val a)) i j := rfl

theorem denote_one {n : Nat} : denote (Circuit.one : Circuit n) = 1 := rfl

theorem denote_seq {n : Nat} (a b : Circuit n) :
    denote (Circuit.seq a b) = denote b * denote a := rfl

theorem denote_gate {n : Nat} (g : Gate n) : denote (Circuit.gate g) = denoteGate g := rfl

/-! ### Every gate is unitary, hence every circuit is unitary -/

theorem denoteGate_isUnitary {n : Nat} (g : Gate n) : IsUnitaryM (denoteGate g) := by
  cases g with
  | h i => exact isUnitaryM_embed1 H2 isUnitary_H2 i
  | x i => exact isUnitaryM_embed1 X2 isUnitary_X2 i
  | y i => exact isUnitaryM_embed1 Y2 isUnitary_Y2 i
  | z i => exact isUnitaryM_embed1 Z2 isUnitary_Z2 i
  | s i => exact isUnitaryM_embed1 S2 isUnitary_S2 i
  | t i => exact isUnitaryM_embed1 T2 isUnitary_T2 i
  | sDag i => exact isUnitaryM_embed1 S2Dag isUnitary_S2Dag i
  | tDag i => exact isUnitaryM_embed1 T2Dag isUnitary_T2Dag i
  | rz i a => exact isUnitaryM_embed1 (Rz2 (Angle.val a)) (isUnitary_Rz2 _) i
  | rx i a => exact isUnitaryM_embed1 (Rx2 (Angle.val a)) (isUnitary_Rx2 _) i
  | ry i a => exact isUnitaryM_embed1 (Ry2 (Angle.val a)) (isUnitary_Ry2 _) i
  | cx i j h => exact isUnitaryM_embed2 CNOT4 isUnitary_CNOT4 h
  | cz i j h => exact isUnitaryM_embed2 CZ4 isUnitary_CZ4 h
  | swap i j h => exact isUnitaryM_embed2 SWAP4 isUnitary_SWAP4 h
  | crz i j h a => exact isUnitaryM_embed2 (CRz4 (Angle.val a)) (isUnitary_CRz4 _) h

/-- Every circuit denotes a unitary operator. -/
theorem denote_isUnitary {n : Nat} (c : Circuit n) : IsUnitaryM (denote c) := by
  induction c with
  | one => exact isUnitaryM_one
  | gate g => exact denoteGate_isUnitary g
  | seq a b ih₁ ih₂ => exact isUnitaryM_mul ih₂ ih₁

/-- The denotation of a circuit is never the zero matrix (it is invertible). -/
theorem denote_ne_zero {n : Nat} (c : Circuit n) : denote c ≠ 0 := by
  classical
  intro h
  have hu := (denote_isUnitary c).1
  rw [h, Matrix.zero_mul] at hu
  have := congrFun (congrFun hu (Classical.arbitrary (Basis n)))
    (Classical.arbitrary (Basis n))
  simp only [Matrix.zero_apply, Matrix.one_apply, Pi.zero_apply, Pi.one_apply] at this
  exact zero_ne_one this

/-! ### Sequential products and the normal form -/

/-- The denotation of a gate list, in the convention that the head gate executes first. -/
noncomputable def prodGate : List (Gate n) -> Operator n
  | [] => 1
  | g :: gs => prodGate gs * denoteGate g

theorem prodGate_append {n : Nat} (gs hs : List (Gate n)) :
    prodGate (gs ++ hs) = prodGate hs * prodGate gs := by
  induction gs with
  | nil => simp [prodGate]
  | cons g t ih =>
    rw [List.cons_append, prodGate, ih, prodGate, ← Matrix.mul_assoc]

theorem denote_ofGates {n : Nat} (gs : List (Gate n)) :
    denote (Circuit.ofGates gs) = prodGate gs := by
  induction gs with
  | nil => rfl
  | cons g t ih =>
    show denote (Circuit.seq (Circuit.gate g) (Circuit.ofGates t)) = prodGate (g :: t)
    rw [denote_seq, ih, prodGate, denote_gate]

/-- Reconstructing a circuit from its gate list preserves its denotation exactly. -/
theorem denote_gates {n : Nat} (c : Circuit n) : denote (Circuit.ofGates c.gates) = denote c := by
  induction c with
  | one => rfl
  | gate g =>
    show denote (Circuit.ofGates [g]) = denote (Circuit.gate g)
    simp [Circuit.ofGates, Circuit.gates, denote_seq, denote_one, Matrix.one_mul]
  | seq a b ih₁ ih₂ =>
    calc denote (Circuit.ofGates (a.gates ++ b.gates))
        = prodGate (a.gates ++ b.gates) := denote_ofGates _
      _ = prodGate b.gates * prodGate a.gates := prodGate_append _ _
      _ = denote (Circuit.ofGates b.gates) * denote (Circuit.ofGates a.gates) := by
        rw [(denote_ofGates _).symm, (denote_ofGates _).symm]
      _ = denote b * denote a := by rw [ih₁, ih₂]
      _ = denote (Circuit.seq a b) := (denote_seq _ _).symm

/-- The normal form preserves the denotation exactly (not merely up to global phase). -/
theorem denote_normalize {n : Nat} (c : Circuit n) : denote (Circuit.normalize c) = denote c :=
  denote_gates c

/-! ### Inverses -/

/-- Exact cancellation of an angle with its negation, in the *exact* symbolic sense: the
underlying real numbers sum to zero.  `ring` closes it after expanding the angle -/
theorem val_neg_add_self (a : Angle) : Angle.val (-a) + Angle.val a = 0 := by
  rw [Angle.val_neg]; ring

theorem val_add_neg_self (a : Angle) : Angle.val a + Angle.val (-a) = 0 := by
  rw [Angle.val_neg]; ring

/-- A primitive gate followed by its inverse denotes the identity. -/
theorem denoteGate_inv_mul {n : Nat} (g : Gate n) :
    denoteGate (Gate.inv g) * denoteGate g = 1 := by
  cases g with
  | h i =>
    show embed1 H2 i * embed1 H2 i = 1
    rw [embed1_mul, H2_mul_H2, embed1_one]
  | x i =>
    show embed1 X2 i * embed1 X2 i = 1
    rw [embed1_mul, X2_mul_X2, embed1_one]
  | y i =>
    show embed1 Y2 i * embed1 Y2 i = 1
    rw [embed1_mul, Y2_mul_Y2, embed1_one]
  | z i =>
    show embed1 Z2 i * embed1 Z2 i = 1
    rw [embed1_mul, Z2_mul_Z2, embed1_one]
  | s i =>
    show embed1 S2Dag i * embed1 S2 i = 1
    rw [embed1_mul, S2Dag_mul_S2, embed1_one]
  | t i =>
    show embed1 T2Dag i * embed1 T2 i = 1
    rw [embed1_mul, T2Dag_mul_T2, embed1_one]
  | sDag i =>
    show embed1 S2 i * embed1 S2Dag i = 1
    rw [embed1_mul, S2_mul_S2Dag, embed1_one]
  | tDag i =>
    show embed1 T2 i * embed1 T2Dag i = 1
    rw [embed1_mul, T2_mul_T2Dag, embed1_one]
  | rz i a =>
    show embed1 (Rz2 (Angle.val (-a))) i * embed1 (Rz2 (Angle.val a)) i = 1
    rw [embed1_mul, Rz2_mul, val_neg_add_self, Rz2_zero, embed1_one]
  | rx i a =>
    show embed1 (Rx2 (Angle.val (-a))) i * embed1 (Rx2 (Angle.val a)) i = 1
    rw [embed1_mul, Rx2_mul, val_neg_add_self, Rx2_zero, embed1_one]
  | ry i a =>
    show embed1 (Ry2 (Angle.val (-a))) i * embed1 (Ry2 (Angle.val a)) i = 1
    rw [embed1_mul, Ry2_mul, val_neg_add_self, Ry2_zero, embed1_one]
  | cx i j hij =>
    show embed2 CNOT4 i j * embed2 CNOT4 i j = 1
    rw [embed2_mul (hij := hij), CNOT4_mul_CNOT4, embed2_one hij]
  | cz i j hij =>
    show embed2 CZ4 i j * embed2 CZ4 i j = 1
    rw [embed2_mul (hij := hij), CZ4_mul_CZ4, embed2_one hij]
  | swap i j hij =>
    show embed2 SWAP4 i j * embed2 SWAP4 i j = 1
    rw [embed2_mul (hij := hij), SWAP4_mul_SWAP4, embed2_one hij]
  | crz i j hij a =>
    show embed2 (CRz4 (Angle.val (-a))) i j * embed2 (CRz4 (Angle.val a)) i j = 1
    rw [embed2_mul (hij := hij), CRz4_mul, val_neg_add_self, CRz4_zero, embed2_one hij]

/-- A primitive gate preceded by its inverse denotes the identity. -/
theorem denoteGate_mul_inv {n : Nat} (g : Gate n) :
    denoteGate g * denoteGate (Gate.inv g) = 1 := by
  cases g with
  | h i =>
    show embed1 H2 i * embed1 H2 i = 1
    rw [embed1_mul, H2_mul_H2, embed1_one]
  | x i =>
    show embed1 X2 i * embed1 X2 i = 1
    rw [embed1_mul, X2_mul_X2, embed1_one]
  | y i =>
    show embed1 Y2 i * embed1 Y2 i = 1
    rw [embed1_mul, Y2_mul_Y2, embed1_one]
  | z i =>
    show embed1 Z2 i * embed1 Z2 i = 1
    rw [embed1_mul, Z2_mul_Z2, embed1_one]
  | s i =>
    show embed1 S2 i * embed1 S2Dag i = 1
    rw [embed1_mul, S2_mul_S2Dag, embed1_one]
  | t i =>
    show embed1 T2 i * embed1 T2Dag i = 1
    rw [embed1_mul, T2_mul_T2Dag, embed1_one]
  | sDag i =>
    show embed1 S2Dag i * embed1 S2 i = 1
    rw [embed1_mul, S2Dag_mul_S2, embed1_one]
  | tDag i =>
    show embed1 T2Dag i * embed1 T2 i = 1
    rw [embed1_mul, T2Dag_mul_T2, embed1_one]
  | rz i a =>
    show embed1 (Rz2 (Angle.val a)) i * embed1 (Rz2 (Angle.val (-a))) i = 1
    rw [embed1_mul, Rz2_mul, val_add_neg_self, Rz2_zero, embed1_one]
  | rx i a =>
    show embed1 (Rx2 (Angle.val a)) i * embed1 (Rx2 (Angle.val (-a))) i = 1
    rw [embed1_mul, Rx2_mul, val_add_neg_self, Rx2_zero, embed1_one]
  | ry i a =>
    show embed1 (Ry2 (Angle.val a)) i * embed1 (Ry2 (Angle.val (-a))) i = 1
    rw [embed1_mul, Ry2_mul, val_add_neg_self, Ry2_zero, embed1_one]
  | cx i j hij =>
    show embed2 CNOT4 i j * embed2 CNOT4 i j = 1
    rw [embed2_mul (hij := hij), CNOT4_mul_CNOT4, embed2_one hij]
  | cz i j hij =>
    show embed2 CZ4 i j * embed2 CZ4 i j = 1
    rw [embed2_mul (hij := hij), CZ4_mul_CZ4, embed2_one hij]
  | swap i j hij =>
    show embed2 SWAP4 i j * embed2 SWAP4 i j = 1
    rw [embed2_mul (hij := hij), SWAP4_mul_SWAP4, embed2_one hij]
  | crz i j hij a =>
    show embed2 (CRz4 (Angle.val a)) i j * embed2 (CRz4 (Angle.val (-a))) i j = 1
    rw [embed2_mul (hij := hij), CRz4_mul, val_add_neg_self, CRz4_zero, embed2_one hij]

/-- The inverse circuit really is a two-sided inverse of the denotation.  This is the
"uncomputation" law: a computation followed by its uncomputation is the identity, and it is
an *exact* matrix identity, not merely an identity up to global phase. -/
theorem denote_inv_mul {n : Nat} (c : Circuit n) : denote (Circuit.inv c) * denote c = 1 := by
  induction c with
  | one =>
    show (1 : Operator n) * 1 = 1
    rw [Matrix.one_mul]
  | gate g => exact denoteGate_inv_mul g
  | seq a b iha ihb =>
    show denote (Circuit.inv (Circuit.seq a b)) * (denote b * denote a) = 1
    simp only [Circuit.inv, denote_seq]
    rw [Matrix.mul_assoc,
      ← Matrix.mul_assoc (denote (Circuit.inv b)) (denote b) (denote a),
      ihb, Matrix.one_mul, iha]

/-- The other side: running a circuit and then its uncomputation is also the identity. -/
theorem denote_mul_inv {n : Nat} (c : Circuit n) : denote c * denote (Circuit.inv c) = 1 := by
  have h := denote_inv_mul (Circuit.inv c)
  simpa [Circuit.inv_inv] using h


/-! ### Realizing the specified action of the primitive gates -/

/-- Two basis states are equal exactly when they agree outside one qubit and coincide on it. -/
theorem ite_congr_prop {α : Type} {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q)
    (a b : α) : (if P then a else b) = (if Q then a else b) := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

theorem basis_eq_iff_agree1 {n : Nat} (i : Fin n) (x y : Basis n) :
    x = y ↔ (agreeOff [i] x y ∧ x i = y i) := by
  constructor
  · intro h
    subst h
    exact ⟨fun a ha => rfl, rfl⟩
  · rintro ⟨h, hi⟩
    funext a
    by_cases ha : a = i
    · rw [ha]
      exact hi
    · exact h a (by simpa using ha)

theorem basis_update_iff {n : Nat} (i : Fin n) (x y : Basis n) :
    x = Function.update y i (!y i) ↔ (agreeOff [i] x y ∧ x i = !y i) := by
  constructor
  · intro h
    subst h
    constructor
    · intro a ha
      rw [Function.update_apply]
      rw [if_neg (by simpa using ha)]
    · rw [Function.update_apply, if_pos rfl]
  · rintro ⟨h, hi⟩
    funext a
    by_cases ha : a = i
    · rw [ha, hi, Function.update_apply, if_pos rfl]
    · rw [h a (by simpa using ha), Function.update_apply, if_neg (by simpa using ha)]

/-- X applied at qubit i flips bit i and leaves every other bit unchanged. -/
theorem denote_x_action {n : Nat} (i : Fin n) (x y : Basis n) :
    (denote (Circuit.gate (Gate.x i)) : Operator n) x y =
      if x = Function.update y i (!y i) then 1 else 0 := by
  classical
  have key := basis_update_iff i x y
  rw [denote_gate, denoteGate_x, embed1_apply, X2_action]
  have h1 : (if agreeOff [i] x y then (if x i = !y i then (1 : ℂ) else 0) else 0)
      = (if agreeOff [i] x y ∧ x i = !y i then (1 : ℂ) else 0) := by
    by_cases h : agreeOff [i] x y <;> by_cases h' : x i = !y i <;> simp [h, h']
  rw [h1, ite_congr_prop key 1 0]

/-- Z applied at qubit i multiplies the |1> component of bit i by -1 and fixes the rest. -/
theorem denote_z_action {n : Nat} (i : Fin n) (x y : Basis n) :
    (denote (Circuit.gate (Gate.z i)) : Operator n) x y =
      if x = y then (if x i then (-1 : ℂ) else 1) else 0 := by
  classical
  have key := basis_eq_iff_agree1 i x y
  rw [denote_gate, denoteGate_z, embed1_apply, Z2_action]
  by_cases h1 : agreeOff [i] x y
  · by_cases h2 : x i = y i
    · rw [if_pos h1, if_pos h2, if_pos (key.mpr ⟨h1, h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (fun hh => h2 ((key.mp hh).2))]
  · rw [if_neg h1, if_neg (fun hh => h1 ((key.mp hh).1))]

/-- CNOT with control i and target j flips bit j exactly when bit i is set, and fixes the rest. -/
theorem denote_cx_action {n : Nat} (i j : Fin n) (hij : i ≠ j) (x y : Basis n) :
    (denote (Circuit.gate (Gate.cx i j hij)) : Operator n) x y =
      if agreeOff [i, j] x y ∧ x i = y i ∧
        x j = (if y i then !y j else y j) then 1 else 0 := by
  classical
  rw [denote_gate, denoteGate_cx, embed2_apply, CNOT4_action]
  have h1 : (if agreeOff [i, j] x y
      then (if (x i, x j) = (y i, if y i then !y j else y j) then (1 : ℂ) else 0) else 0)
      = (if agreeOff [i, j] x y ∧
          (x i, x j) = (y i, if y i then !y j else y j) then (1 : ℂ) else 0) := by
    by_cases h : agreeOff [i, j] x y <;>
      by_cases h' : (x i, x j) = (y i, if y i then !y j else y j) <;> simp [h, h']
  rw [h1]
  refine ite_congr_prop ?_ 1 0
  constructor
  · rintro ⟨h, hp⟩
    rw [Prod.mk.injEq] at hp
    obtain ⟨hi, hj⟩ := hp
    exact ⟨h, hi, hj⟩
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨hi, hj⟩

/-- SWAP exchanges the two bits it acts on and fixes the rest. -/
theorem denote_swap_action {n : Nat} (i j : Fin n) (hij : i ≠ j) (x y : Basis n) :
    (denote (Circuit.gate (Gate.swap i j hij)) : Operator n) x y =
      if agreeOff [i, j] x y ∧ x i = y j ∧ x j = y i then 1 else 0 := by
  classical
  rw [denote_gate, denoteGate_swap, embed2_apply, SWAP4_action]
  have h1 : (if agreeOff [i, j] x y
      then (if (x i, x j) = (y j, y i) then (1 : ℂ) else 0) else 0)
      = (if agreeOff [i, j] x y ∧ (x i, x j) = (y j, y i) then (1 : ℂ) else 0) := by
    by_cases h : agreeOff [i, j] x y <;>
      by_cases h' : (x i, x j) = (y j, y i) <;> simp [h, h']
  rw [h1]
  refine ite_congr_prop ?_ 1 0
  constructor
  · rintro ⟨h, hp⟩
    rw [Prod.mk.injEq] at hp
    obtain ⟨hi, hj⟩ := hp
    exact ⟨h, hi, hj⟩
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨hi, hj⟩

end Quantum