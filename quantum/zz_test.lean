import Quantum.Optimizer

open Quantum Quantum.Opt

def i0 : Fin 1 := ⟨0, by decide⟩
def j0 : Fin 2 := ⟨0, by decide⟩
def j1 : Fin 2 := ⟨1, by decide⟩
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

-- Example A: H(0);H(0)
def cA : Circuit 1 := Circuit.ofGates [Gate.h i0, Gate.h i0]
-- Example B: CNOT(0,1);CNOT(0,1)
def cB : Circuit 2 := Circuit.ofGates [Gate.cx j0 j1 (by decide), Gate.cx j0 j1 (by decide)]
-- Example C: S;S and T;T
def cC : Circuit 1 := Circuit.ofGates [Gate.s i0, Gate.s i0, Gate.t i0, Gate.t i0]
-- Example F: X Z X Z
def cF : Circuit 1 := Circuit.ofGates [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]
-- Example I: CNOT(0,1) ; X(2) ; CNOT(0,1)
def cI : Circuit 3 :=
  Circuit.ofGates [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)]

#eval (Cost.of cA, Cost.of cB, Cost.of cC, Cost.of cF, Cost.of cI)

def showOpt {n : Nat} (label : String) (c : Circuit n) : IO Unit := do
  match optimize Config.default c with
  | none => IO.println s! "{label}: none"
  | some (c', cert) =>
      IO.println s! "{label}: gates {c.gates.length} -> {c'.gates.length}; cert steps {cert.length}; checked {checkCertificate c c' cert}"

#eval showOpt "A (H;H)" cA
#eval showOpt "B (CNOT;CNOT)" cB
#eval showOpt "C (S;S;T;T)" cC
#eval showOpt "F (X Z X Z)" cF
#eval showOpt "I (CX X CX)" cI
