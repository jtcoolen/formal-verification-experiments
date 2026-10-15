/-
Explicit, mathematically defined cost model.

Three independent resource measurements are defined on circuits:

* gateCount     - number of primitive gate occurrences (identity contributes zero)
* twoQubitCount - number of two-qubit gates (cx, cz, swap, crz)
* tCount        - number of T and T-dagger gates

All three are additive under sequential composition, and the optimizer compares circuits
with a lexicographic order whose priority is part of the configuration.

IMPORTANT: these are abstract gate counts.  They are NOT hardware execution time, error
rates, or physical implementation cost, and no theorem in this project claims otherwise.
-/
import Quantum.Syntax

namespace Quantum

/-- The three resource measurements of a circuit. -/
structure Cost where
  gateCount : Nat
  twoQubitCount : Nat
  tCount : Nat
deriving Repr, Inhabited, DecidableEq, BEq

instance : Add Cost := ⟨fun a b => ⟨a.gateCount + b.gateCount,
  a.twoQubitCount + b.twoQubitCount, a.tCount + b.tCount⟩⟩
instance : Zero Cost := ⟨⟨0, 0, 0⟩⟩

@[ext] theorem Cost.ext : ∀ {a b : Cost}, a.gateCount = b.gateCount ->
    a.twoQubitCount = b.twoQubitCount -> a.tCount = b.tCount -> a = b := by
  intro a b h1 h2 h3
  cases a with | mk x1 x2 x3 => cases b with | mk y1 y2 y3 =>
    simp only [Cost.mk.injEq] at *
    exact ⟨h1, h2, h3⟩

@[simp] theorem add_gateCount (a b : Cost) : (a + b).gateCount = a.gateCount + b.gateCount := rfl
@[simp] theorem add_twoQubitCount (a b : Cost) :
    (a + b).twoQubitCount = a.twoQubitCount + b.twoQubitCount := rfl
@[simp] theorem add_tCount (a b : Cost) : (a + b).tCount = a.tCount + b.tCount := rfl
@[simp] theorem zero_gateCount : (0 : Cost).gateCount = 0 := rfl
@[simp] theorem zero_twoQubitCount : (0 : Cost).twoQubitCount = 0 := rfl
@[simp] theorem zero_tCount : (0 : Cost).tCount = 0 := rfl

/-- Which resource a comparison looks at, in priority order. -/
inductive CostKey : Type
  | gateCount | twoQubitCount | tCount
deriving Repr, Inhabited, DecidableEq, BEq

/-- A cost policy: the lexicographic priority order of the three resources.
The first component of 'keys' is the most significant. -/
structure CostConfig where
  keys : List CostKey
deriving Repr, Inhabited

/-- The default policy: gate count, then two-qubit count, then T count. -/
def CostConfig.default : CostConfig :=
  { keys := [CostKey.gateCount, CostKey.twoQubitCount, CostKey.tCount] }

namespace Cost

/-- The local cost of a single gate. -/
def ofGate (g : Gate n) : Cost :=
  { gateCount := 1
    twoQubitCount := if g.isTwoQubit then 1 else 0
    tCount := if g.kind = GateKind.t || g.kind = GateKind.tDag then 1 else 0 }

/-- The cost of a circuit: additive over sequential composition. -/
def of : Circuit n -> Cost
  | Circuit.one => 0
  | Circuit.seq a b => of a + of b
  | Circuit.gate g => ofGate g

def ofGates : List (Gate n) -> Cost
  | [] => 0
  | g :: gs => ofGate g + ofGates gs

/-- The component of a cost selected by a key. -/
def get (k : CostKey) (c : Cost) : Nat :=
  match k with
  | CostKey.gateCount => c.gateCount
  | CostKey.twoQubitCount => c.twoQubitCount
  | CostKey.tCount => c.tCount

/-- The cost projected onto the priority order of a policy. -/
def project (cfg : CostConfig) (c : Cost) : List Nat := cfg.keys.map (fun k => get k c)

/-- Lexicographic comparison of the projected costs. -/
def le (cfg : CostConfig) (a b : Cost) : Bool := (project cfg a).lex (project cfg b)

/-- Strict lexicographic comparison of the projected costs. -/
def lt (cfg : CostConfig) (a b : Cost) : Bool := le cfg a b && !(le cfg b a)

theorem ofGates_append (gs hs : List (Gate n)) :
    ofGates (gs ++ hs) = ofGates gs + ofGates hs := by
  induction gs with
  | nil => ext <;> simp [ofGates]
  | cons g t ih => ext <;> simp [ofGates, ih, add_assoc]

theorem of_ofGates (gs : List (Gate n)) : of (Circuit.ofGates gs) = ofGates gs := by
  induction gs with
  | nil => rfl
  | cons g t ih => simp [Circuit.ofGates, of, ofGates, ih]

theorem of_gates (c : Circuit n) : of c = ofGates c.gates := by
  induction c with
  | one => rfl
  | gate g => rfl
  | seq a b ih₁ ih₂ =>
    simp [of, ih₁, ih₂, ofGates_append, Circuit.gates, Circuit.seq]

theorem of_le (cfg : CostConfig) (c : Circuit n) : 0 ≤ (of c).gateCount := Nat.zero_le _

end Cost

end Quantum