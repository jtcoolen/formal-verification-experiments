/-
Explicit target-architecture specification and resource accounting.

The accounting model follows the fault-tolerant *spacetime* metric used by the ECDSA.Fail
benchmark for reversible elliptic-curve point addition (arXiv:2609.09582, section 3.2): two
resources are reported,

* `qubitWidth c` - the peak number of logically live qubits: the maximum, over program
  points, of the number of qubits touched at or after that point;
* `toffoliCount c` - the number of Toffoli-equivalent operations,

and the headline score is their product, `spacetimeScore c = qubitWidth c * toffoliCount c`.

IMPORTANT, and deliberately stated: these are *abstract* counts over the gate library of this
project.  They are not hardware execution time, not error rates, not a magic-state
distillation cost, and not a claim about any physical device.  The mapping from a gate of
`Quantum.Gate` to a Toffoli-equivalent cost is an explicit definition (`toffoliEquiv`), so the
accounting formula lives inside the verified artifact rather than being assumed.

This module also keeps separate the three claims that must not be conflated:
1. semantic preservation - Quantum/Certificates.lean, Quantum/Correctness.lean;
2. architectural support - decidable here via `Architecture.supportsGate`;
3. cost accounting - `Cost.of` plus the functions here, always computed *from the circuit
   that is actually returned*.
-/
import Quantum.Cost

namespace Quantum

/-! ### The declared architecture -/

/-- A fault-tolerant architecture specification: which gate kinds it provides, and how many
Toffoli-equivalent operations each kind costs.

The Toffoli-equivalent convention follows ECDSA.Fail, where each executed CCX or CCZ counts as
one Toffoli-equivalent.  This gate library has no native Toffoli, so the two-qubit gates (CX,
CZ, SWAP, CRZ) play that role and single-qubit gates cost zero.  A gate kind that is not
`supported` is unavailable on this architecture; no rewrite rule in Quantum/Rewrites.lean
introduces one, so the optimizer can never emit an unsupported gate. -/
structure Architecture where
  toffoliEquiv : GateKind → Nat
  supported : GateKind → Bool

namespace Architecture

/-- The declared reference architecture: every gate kind of the library is native, and the
two-qubit gates are the Toffoli-equivalent ones. -/
def default : Architecture where
  toffoliEquiv := fun k =>
    match k with
    | GateKind.cx => 1
    | GateKind.cz => 1
    | GateKind.swap => 1
    | GateKind.crz => 1
    | GateKind.cp => 1
    | _ => 0
  supported := fun _ => true

/-- A Clifford-only architecture: controlled rotations are not available, so a circuit using
one is *not* implementable on it and must be rejected rather than silently approximated. -/
def clifford : Architecture where
  toffoliEquiv := fun k =>
    match k with
    | GateKind.cx => 1
    | GateKind.cz => 1
    | GateKind.swap => 1
    | _ => 0
  supported := fun k =>
    match k with
    | GateKind.crz => false
    | GateKind.cp => false
    | GateKind.t => false
    | GateKind.tDag => false
    | _ => true

/-- Does the architecture provide the gate `g`? -/
def supportsGate (A : Architecture) (g : Gate n) : Bool := A.supported g.kind

/-- Does the architecture provide every gate of the circuit? -/
def supports (A : Architecture) (c : Circuit n) : Bool :=
  c.gates.all fun g => A.supportsGate g

end Architecture

/-! ### Toffoli-equivalent count -/

/-- The Toffoli-equivalent cost of one gate under an architecture. -/
def toffoliEquivGate (A : Architecture) (g : Gate n) : Nat := A.toffoliEquiv g.kind

/-- The Toffoli-equivalent count of a circuit: additive over sequential composition. -/
def toffoliCount (A : Architecture) : Circuit n → Nat
  | Circuit.one => 0
  | Circuit.seq a b => toffoliCount A a + toffoliCount A b
  | Circuit.gate g => toffoliEquivGate A g

def toffoliGates (A : Architecture) : List (Gate n) → Nat
  | [] => 0
  | g :: gs => toffoliEquivGate A g + toffoliGates A gs

theorem toffoliGates_append (A : Architecture) (gs hs : List (Gate n)) :
    toffoliGates A (gs ++ hs) = toffoliGates A gs + toffoliGates A hs := by
  induction gs with
  | nil => simp [toffoliGates]
  | cons g t ih => simp [toffoliGates, ih, add_assoc]

theorem toffoli_ofGates (A : Architecture) (gs : List (Gate n)) :
    toffoliCount A (Circuit.ofGates gs) = toffoliGates A gs := by
  induction gs with
  | nil => rfl
  | cons g t ih => simp [Circuit.ofGates, toffoliCount, toffoliGates, ih]

theorem toffoli_gates (A : Architecture) (c : Circuit n) :
    toffoliCount A c = toffoliGates A c.gates := by
  induction c with
  | one => rfl
  | gate g => rfl
  | seq a b ih₁ ih₂ => simp [toffoliCount, Circuit.gates, ih₁, ih₂, toffoliGates_append]

/-- Toffoli count is monotone under appending gates. -/
theorem toffoliGates_le_append (A : Architecture) (gs hs : List (Gate n)) :
    toffoliGates A gs ≤ toffoliGates A (gs ++ hs) := by
  induction gs with
  | nil => simp [toffoliGates]
  | cons g t ih => simp [toffoliGates, ih, Nat.le_add_right]

/-! ### Logical width -/

/-- The qubits a circuit touches. -/
def usedQubits {n : Nat} (c : Circuit n) : Finset (Fin n) :=
  (c.gates.flatMap fun g => g.qubits).toFinset

/-- The logical width Q of a circuit: the number of qubits it touches.  This is an upper bound
on the peak number of simultaneously live qubits (a qubit can only be live between its first
and its last use), and it is the quantity the declared cost model charges space for. -/
def qubitWidth {n : Nat} (c : Circuit n) : Nat := (usedQubits c).card

/-- The Toffoli-equivalent count of a circuit under the declared architecture; this is the Q
of the ECDSA.Fail metric paired with the width below. -/
def toffoliT {n : Nat} (c : Circuit n) : Nat := toffoliCount Architecture.default c

/-- The spacetime score S = Q * T of a circuit: lower is better. -/
def spacetimeScore {n : Nat} (c : Circuit n) : Nat := qubitWidth c * toffoliT c


/-! ### Elementary properties of the accounting -/

/-- The logical width never exceeds the register size. -/
theorem qubitWidth_le {n : Nat} (c : Circuit n) : qubitWidth c ≤ n := by
  classical
  exact (Finset.card_le_univ _).trans (by simp [Fintype.card_fin])

theorem width_one {n : Nat} : qubitWidth (Circuit.one : Circuit n) = 0 := rfl

theorem toffoli_one {n : Nat} : toffoliT (Circuit.one : Circuit n) = 0 := rfl

theorem score_one {n : Nat} : spacetimeScore (Circuit.one : Circuit n) = 0 := rfl

/-- Adding a block cannot decrease the Toffoli count. -/
theorem toffoliCount_le_seq (A : Architecture) (a b : Circuit n) :
    toffoliCount A a ≤ toffoliCount A (Circuit.seq a b) := by
  simp [toffoliCount]

/-- The declared default architecture supports every gate of the library. -/
theorem supports_default {n : Nat} (c : Circuit n) :
    Architecture.supports Architecture.default c = true := by
  classical
  suffices h : ∀ gs : List (Gate n), (gs.all fun g => Architecture.default.supported g.kind) = true by
    simpa [Architecture.supports] using h c.gates
  intro gs
  induction gs with
  | nil => rfl
  | cons g t ih => simp [List.all_cons, Architecture.default]

/-- The Clifford-only architecture really does refuse a controlled rotation: the check is a
decision procedure, not a decoration. -/
theorem clifford_refuses_crz :
    Architecture.supports Architecture.clifford
      (Circuit.gate (Gate.crz (⟨0, by decide⟩ : Fin 2) (⟨1, by decide⟩ : Fin 2)
        (by decide) Angle.pi) : Circuit 2) = false := by decide

end Quantum
