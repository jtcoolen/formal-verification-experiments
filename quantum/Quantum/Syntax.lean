/-
Quantum circuit syntax, indexed by the number of qubits.

* 'Gate n' is the set of primitive gates on an n-qubit register.  Qubit references are
  'Fin n', and the two-qubit gates carry a proof that their two indices are distinct, so
  malformed qubit references and illegal two-qubit placements are unrepresentable.
* 'Circuit n' is a deeply embedded syntax: identity, sequential composition and gates.
  The composition convention is: 'seq a b' executes a first and then b.
-/
import Quantum.Angle

namespace Quantum

/-! ### Primitive gates -/

inductive Gate (n : Nat) : Type where
  | h : Fin n -> Gate n
  | x : Fin n -> Gate n
  | y : Fin n -> Gate n
  | z : Fin n -> Gate n
  | s : Fin n -> Gate n
  | t : Fin n -> Gate n
  | sDag : Fin n -> Gate n
  | tDag : Fin n -> Gate n
  | rz : Fin n -> Angle -> Gate n
  | rx : Fin n -> Angle -> Gate n
  | ry : Fin n -> Angle -> Gate n
  | cx : (c : Fin n) -> (t : Fin n) -> c ≠ t -> Gate n
  | cz : (c : Fin n) -> (t : Fin n) -> c ≠ t -> Gate n
  | swap : (a : Fin n) -> (b : Fin n) -> a ≠ b -> Gate n
  | crz : (c : Fin n) -> (t : Fin n) -> c ≠ t -> Angle -> Gate n
  | cp : (c : Fin n) -> (t : Fin n) -> c ≠ t -> Angle -> Gate n
deriving DecidableEq, Repr

/-- The sort of a gate, used by the architecture specification and by the cost model. -/
inductive GateKind : Type where
  | h | x | y | z | s | t | sDag | tDag | rz | rx | ry | cx | cz | swap | crz | cp
deriving DecidableEq

/-! ### Circuits -/

inductive Circuit (n : Nat) : Type where
  | one : Circuit n
  | seq : Circuit n -> Circuit n -> Circuit n
  | gate : Gate n -> Circuit n
deriving DecidableEq, Repr

namespace Gate

def qubits : Gate n -> List (Fin n)
  | h i | x i | y i | z i | s i | t i | sDag i | tDag i => [i]
  | cx i j _ | cz i j _ | swap i j _ => [i, j]
  | rz i _ | rx i _ | ry i _ => [i]
  | crz i j _ _ => [i, j]
  | cp i j _ _ => [i, j]

def kind : Gate n -> GateKind
  | h _ => GateKind.h
  | x _ => GateKind.x
  | y _ => GateKind.y
  | z _ => GateKind.z
  | s _ => GateKind.s
  | t _ => GateKind.t
  | sDag _ => GateKind.sDag
  | tDag _ => GateKind.tDag
  | rz _ _ => GateKind.rz
  | rx _ _ => GateKind.rx
  | ry _ _ => GateKind.ry
  | cx _ _ _ => GateKind.cx
  | cz _ _ _ => GateKind.cz
  | swap _ _ _ => GateKind.swap
  | crz _ _ _ _ => GateKind.crz
  | cp _ _ _ _ => GateKind.cp

/-- The index of a single-qubit gate, if it is one. -/
def index1? : Gate n -> Option (Fin n)
  | h i | x i | y i | z i | s i | t i | sDag i | tDag i => some i
  | rz i _ | rx i _ | ry i _ => some i
  | _ => none

/-- The (control, target) indices of a two-qubit gate, if it is one. -/
def index2? : Gate n -> Option (Fin n × Fin n)
  | cx i j _ | cz i j _ | swap i j _ => some (i, j)
  | crz i j _ _ => some (i, j)
  | cp i j _ _ => some (i, j)
  | _ => none

def isOneQubit (g : Gate n) : Bool := g.index1?.isSome
def isTwoQubit (g : Gate n) : Bool := g.index2?.isSome

/-- Does the gate touch qubit 'i'? -/
def touches (g : Gate n) (i : Fin n) : Bool := g.qubits.contains i

end Gate

/-! ### Inverses -/

/-- The primitive gate that undoes a primitive gate.  Every gate is its own inverse except
that 'S', 'T' and the rotations flip sign / take the dagger, so 'inv' is an involution on
gates and 'denote (inv g) * denote g = 1' (proved in Quantum/Semantics.lean). -/
def Gate.inv : Gate n -> Gate n
  | h i => h i
  | x i => x i
  | y i => y i
  | z i => z i
  | s i => sDag i
  | t i => tDag i
  | sDag i => s i
  | tDag i => t i
  | rz i a => rz i (-a)
  | rx i a => rx i (-a)
  | ry i a => ry i (-a)
  | cx i j hij => cx i j hij
  | cz i j hij => cz i j hij
  | swap i j hij => swap i j hij
  | crz i j hij a => crz i j hij (-a)
  | cp i j hij a => cp i j hij (-a)

theorem Gate.inv_inv (g : Gate n) : Gate.inv (Gate.inv g) = g := by
  cases g <;> simp [Gate.inv, Angle.neg_neg]

namespace Circuit

infixl:70 " ; " => Circuit.seq

/-- Build a circuit from a list of gates: right-nested, terminated by 'Circuit.one'. -/
def ofGates : List (Gate n) -> Circuit n
  | [] => Circuit.one
  | g :: gs => Circuit.seq (Circuit.gate g) (ofGates gs)

/-- The gates of a circuit, in execution order. -/
def gates : Circuit n -> List (Gate n)
  | one => []
  | seq a b => a.gates ++ b.gates
  | gate g => [g]

/-- All subcircuits, in a preorder traversal (the circuit itself first). -/
def subcircuits : Circuit n -> List (Circuit n)
  | one => [Circuit.one]
  | gate g => [Circuit.gate g]
  | seq a b => Circuit.seq a b :: a.subcircuits ++ b.subcircuits

/-- Number of syntax nodes. -/
def nodeCount : Circuit n -> Nat
  | one => 1
  | seq a b => a.nodeCount + b.nodeCount + 1
  | gate _ => 1

/-- Depth of the syntax tree. -/
def depth : Circuit n -> Nat
  | one => 0
  | gate _ => 0
  | seq a b => max a.depth b.depth + 1

/-- The circuit that undoes 'c': the gate list is reversed and every gate is inverted. -/
def inv : Circuit n -> Circuit n
  | one => one
  | gate g => gate (Gate.inv g)
  | seq a b => seq b.inv a.inv

/-- The gate list of an inverse circuit: the reverse of the gate list, each gate inverted. -/
theorem gates_inv (c : Circuit n) : c.inv.gates = c.gates.reverse.map Gate.inv := by
  induction c with
  | one => rfl
  | gate g => rfl
  | seq a b ih₁ ih₂ =>
    simp only [Circuit.inv, Circuit.gates, ih₁, ih₂, List.reverse_append, List.map_append]

/-- Inverting twice is the identity. -/
theorem inv_inv (c : Circuit n) : Circuit.inv (Circuit.inv c) = c := by
  induction c with
  | one => rfl
  | gate g =>
    show Circuit.gate (Gate.inv (Gate.inv g)) = Circuit.gate g
    rw [Gate.inv_inv]
  | seq a b ih₁ ih₂ => simp only [Circuit.inv, ih₁, ih₂]

/-- The number of gates is preserved by inversion. -/
theorem gates_length_inv (c : Circuit n) : c.inv.gates.length = c.gates.length := by
  rw [gates_inv, List.length_map, List.length_reverse]
/-- The normal form of a circuit: the right-nested gate list.  'Circuit.normalize' is
    proved semantics-preserving in 'Quantum.Semantics' (exact equality, not just up to
    global phase). -/
def normalize : Circuit n -> Circuit n
  | c => ofGates c.gates

end Circuit


/-! ### Executable pretty printing

Purely diagnostic helpers: no theorem in this project depends on them, so they cannot widen
the trust boundary, but they let the command-line tools (and the reader of a certificate)
see what a circuit actually is. -/

/-- The name of a gate as a string. -/
def Gate.show : Gate n -> String
  | Gate.h _ => "H"
  | Gate.x _ => "X"
  | Gate.y _ => "Y"
  | Gate.z _ => "Z"
  | Gate.s _ => "S"
  | Gate.t _ => "T"
  | Gate.sDag _ => "S†"
  | Gate.tDag _ => "T†"
  | Gate.rz _ a => "Rz(" ++ toString a.rat ++ "+" ++ toString a.piQ ++ "pi)"
  | Gate.rx _ a => "Rx(" ++ toString a.rat ++ "+" ++ toString a.piQ ++ "pi)"
  | Gate.ry _ a => "Ry(" ++ toString a.rat ++ "+" ++ toString a.piQ ++ "pi)"
  | Gate.cx i j _ => "CX(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.cz i j _ => "CZ(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.swap i j _ => "SWAP(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.cp i j _ a => "CP(" ++ toString i.val ++ "," ++ toString j.val ++ "," ++ toString a.piQ ++ "pi)"
  | Gate.crz i j _ a => "CRz(" ++ toString i.val ++ "," ++ toString j.val ++ "," ++ toString a.piQ ++ "pi)"

/-- A circuit printed as its gate list in execution order. -/
def Circuit.show (c : Circuit n) : String :=
  String.intercalate " ; " (c.gates.map Gate.show)

end Quantum
