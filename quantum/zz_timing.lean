import Quantum.Optimizer
open Quantum Quantum.Opt

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in

def i0 : Fin 1 := ⟨0, by decide⟩
def j0 : Fin 2 := ⟨0, by decide⟩
def j1 : Fin 2 := ⟨1, by decide⟩
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

def cA : Circuit 1 := Circuit.ofGates [Gate.h i0, Gate.h i0]
def cB : Circuit 2 := Circuit.ofGates [Gate.cx j0 j1 (by decide), Gate.cx j0 j1 (by decide)]
def cC : Circuit 1 := Circuit.ofGates [Gate.s i0, Gate.s i0, Gate.t i0, Gate.t i0]
def cF : Circuit 1 := Circuit.ofGates [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]
def cI : Circuit 3 :=
  Circuit.ofGates [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)]

def report {n : Nat} (label : String) (c : Circuit n) : String :=
  match optimize Config.default c with
  | none => label ++ ": none"
  | some (c', cert) =>
      label ++ ": gates " ++ toString c.gates.length ++ " -> " ++ toString c'.gates.length ++
      ", tcount " ++ toString (Cost.of c).tCount ++ " -> " ++ toString (Cost.of c').tCount ++
      ", 2q " ++ toString (Cost.of c).twoQubitCount ++ " -> " ++
      toString (Cost.of c').twoQubitCount ++
      ", cert " ++ toString cert.length ++ " steps, checked = " ++
      toString (checkCertificate c c' cert)

#eval (quantumRules cA).length
#eval report "A  H;H        " cA
#eval report "B  CX;CX      " cB
#eval report "C  S;S;T;T    " cC
#eval report "F  X;Z;X;Z    " cF
#eval report "I  CX;X;CX    " cI
