/-
Classical-control specialization: the verified form of the "constant propagation" pass of
arXiv:2609.09582 (section 5.3.6).

In a quantum-by-classical arithmetic circuit (schoolbook modular multiplication is the standard
example: xy = sum_i y_i * (2^i x), so each block is executed only when the *classically known*
multiplier bit y_i is 1), the control is a classical bit, not a qubit.  A block whose control
bit is known can therefore be replaced by the block itself (bit = 1) or removed entirely
(bit = 0).  That replacement is *exact*: it is not an approximation and it carries no error
budget, and it is what the ECDSA.Fail leaderboard records as reducing the average executed
Toffoli count.

This is the mirror image of Quantum/ControlPhase.lean: a *quantum* control turns a global phase
into a relative phase and forbids the same simplification, whereas a classical control keeps
the phase global.  Both facts are proved, in their respective files.
-/
import Quantum.Equivalence
import Quantum.Semantics
import Quantum.Cost
import Quantum.Architecture

namespace Quantum

open Classical

/-- A classically-controlled block: run 'c' exactly when the classical bit 'b' is set.  No
qubit is involved in the choice, so this is *not* a controlled operation. -/
def cblock {n : Nat} (b : Bool) (c : Circuit n) : Circuit n :=
  if b then c else Circuit.one

theorem cblock_true {n : Nat} (c : Circuit n) : denote (cblock true c) = denote c := rfl

/-- A block with a classically false control denotes the identity *exactly*. -/
theorem cblock_false {n : Nat} (c : Circuit n) : denote (cblock false c) = 1 := rfl

/-- Classical control preserves phase equivalence in both branches: unlike quantum control, no
relative phase can appear, because the choice does not depend on the quantum state. -/
theorem cblock_phase {n : Nat} (b : Bool) {c c' : Circuit n} (h : PhaseEquivalent c c') :
    PhaseEquivalent (cblock b c) (cblock b c') := by
  cases b with
  | true => simpa [cblock] using h
  | false => simpa [cblock] using PhaseEquivalent.refl (Circuit.one : Circuit n)

/-- The sequential execution of a list of circuits, first element executed first. -/
def exec {n : Nat} : List (Circuit n) → Circuit n
  | [] => Circuit.one
  | c :: cs => Circuit.seq c (exec cs)

/-- The operator product of a list of circuits, first element applied first. -/
noncomputable def prodC {n : Nat} : List (Circuit n) → Operator n
  | [] => 1
  | c :: cs => prodC cs * denote c

theorem denote_exec {n : Nat} (cs : List (Circuit n)) : denote (exec cs) = prodC cs := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    show denote (exec t) * denote c = prodC (c :: t)
    rw [ih, prodC]

/-- A classically-controlled block list: the shape of a quantum-by-classical multiplier. -/
def condBlocks {n : Nat} : List (Bool × Circuit n) → Circuit n
  | [] => Circuit.one
  | (b, c) :: rest => Circuit.seq (cblock b c) (condBlocks rest)

/-- **Constant propagation** (arXiv:2609.09582 section 5.3.6).  Blocks whose classical control
bit is 0 are dropped; blocks whose bit is 1 are kept unconditionally. -/
def constProp {n : Nat} : List (Bool × Circuit n) → List (Circuit n)
  | [] => []
  | (b, c) :: rest => if b then c :: constProp rest else constProp rest

/-- Constant propagation preserves the implemented unitary *exactly*. -/
theorem denote_condBlocks {n : Nat} (l : List (Bool × Circuit n)) :
    denote (condBlocks l) = prodC (constProp l) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨b, c⟩ := p
    show denote (condBlocks t) * denote (cblock b c) = prodC (constProp ((b, c) :: t))
    rw [ih]
    cases b with
    | true => rw [cblock_true, show constProp ((true, c) :: t) = c :: constProp t from rfl, prodC]
    | false =>
      rw [cblock_false, show constProp ((false, c) :: t) = constProp t from rfl, Matrix.mul_one]

/-- Constant propagation preserves the implemented unitary, stated as an equality between the
specialized circuit and the original classically-controlled circuit. -/
theorem denote_constProp_eq {n : Nat} (l : List (Bool × Circuit n)) :
    denote (condBlocks l) = denote (exec (constProp l)) := by
  rw [denote_condBlocks, (denote_exec _).symm]

/-- The specialized circuit is phase-equivalent to the classically-controlled one - and, in
fact, denotationally *equal* to it. -/
theorem constProp_eqExact {n : Nat} (l : List (Bool × Circuit n)) :
    EqExact (condBlocks l) (exec (constProp l)) := denote_constProp_eq l

/-- The gate count never increases under constant propagation. -/
theorem cost_constProp_le {n : Nat} (l : List (Bool × Circuit n)) :
    (Cost.of (exec (constProp l))).gateCount ≤ (Cost.of (condBlocks l)).gateCount := by
  classical
  induction l with
  | nil => simp [condBlocks, constProp, exec, Cost.of]
  | cons p t ih =>
    obtain ⟨b, c⟩ := p
    cases b with
    | true =>
      show (Cost.of (exec (c :: constProp t))).gateCount
        ≤ (Cost.of (Circuit.seq (cblock true c) (condBlocks t))).gateCount
      simp [cblock, exec, condBlocks, constProp, Cost.of, ih, Nat.add_le_add_iff_right]
    | false =>
      show (Cost.of (exec (constProp t))).gateCount
        ≤ (Cost.of (Circuit.seq (cblock false c) (condBlocks t))).gateCount
      simp [cblock, exec, condBlocks, constProp, Cost.of, ih]

/-- The Toffoli-equivalent count never increases under constant propagation: this is exactly
the resource the ECDSA.Fail metric counts. -/
theorem toffoli_constProp_le (A : Architecture) (l : List (Bool × Circuit n)) :
    toffoliCount A (exec (constProp l)) ≤ toffoliCount A (condBlocks l) := by
  classical
  induction l with
  | nil => simp [condBlocks, constProp, exec, toffoliCount]
  | cons p t ih =>
    obtain ⟨b, c⟩ := p
    cases b with
    | true =>
      simp [cblock, exec, condBlocks, constProp, toffoliCount, ih, Nat.add_le_add_iff_right]
    | false =>
      simp [cblock, exec, condBlocks, constProp, toffoliCount, ih]


/-! ### Constant propagation, measured against the unspecialized program -/

/-- The *static* gate count of a guarded block list: what the program would cost if every block
were emitted regardless of its classical guard.  This is the quantity the ECDSA.Fail pass
reduces: the guard is known at compile time, so a block guarded by 0 is never emitted. -/
def staticGateCount {n : Nat} (l : List (Bool × Circuit n)) : Nat :=
  (l.map fun (_, c) => (Cost.of c).gateCount).sum

/-- The static Toffoli-equivalent count of a guarded block list. -/
def staticToffoli {n : Nat} (A : Architecture) (l : List (Bool × Circuit n)) : Nat :=
  (l.map fun (_, c) => toffoliCount A c).sum

/-- A four-step double-and-add ladder with the classical multiplier 13 = 1101 (least
significant bit first): the third guard is 0, so that block is never emitted. -/
def bits13 : List Bool := [true, true, false, true]

/-- The four ladder blocks: two of them are Toffoli-equivalent controlled operations. -/
def blocks13 : List (Circuit 2) :=
  [Circuit.gate (Gate.cx (⟨0, by decide⟩ : Fin 2) (⟨1, by decide⟩ : Fin 2) (by decide)),
   Circuit.gate (Gate.x (⟨0, by decide⟩ : Fin 2)),
   Circuit.gate (Gate.cx (⟨0, by decide⟩ : Fin 2) (⟨1, by decide⟩ : Fin 2) (by decide)),
   Circuit.gate (Gate.h (⟨1, by decide⟩ : Fin 2))]

/-- The guarded ladder as written, and the ladder after constant propagation. -/
def ladder : Circuit 2 := condBlocks (bits13.zip blocks13)

def ladderSpec : Circuit 2 := exec (constProp (bits13.zip blocks13))

/-- Emitting every block costs 4 gates and 2 Toffoli-equivalents; after constant propagation
the ladder has 3 gates and 1 Toffoli-equivalent - a strict reduction, obtained by an *exact*
specialization rather than an approximation. -/
theorem ladder_static : staticGateCount (bits13.zip blocks13) = 4 ∧
    staticToffoli Architecture.default (bits13.zip blocks13) = 2 := by decide

theorem ladder_after : (Cost.of ladderSpec).gateCount = 3 ∧
    toffoliT ladderSpec = 1 := by decide

theorem ladder_saves : (Cost.of ladderSpec).gateCount < staticGateCount (bits13.zip blocks13) ∧
    toffoliT ladderSpec < staticToffoli Architecture.default (bits13.zip blocks13) := by decide

/-- And the specialization is *exactly* the same unitary. -/
theorem ladder_exact : EqExact ladder ladderSpec := denote_constProp_eq (bits13.zip blocks13)

/-- Consequently it is phase-equivalent, which is what the certificate machinery consumes. -/
theorem ladder_phase : PhaseEquivalent ladder ladderSpec :=
  PhaseEquivalent.of_eqExact ladder_exact

end Quantum
