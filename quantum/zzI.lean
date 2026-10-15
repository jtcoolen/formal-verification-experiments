import Quantum.Optimizer
open Quantum Quantum.Opt
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩
def cI : Circuit 3 := Circuit.ofGates [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)]
#eval (quantumRules cI).length
#eval (oneStepRewrites cI).length
