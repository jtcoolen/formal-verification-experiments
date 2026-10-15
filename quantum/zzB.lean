import Quantum.Optimizer
open Quantum Quantum.Opt
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
def j0 : Fin 2 := ⟨0, by decide⟩
def j1 : Fin 2 := ⟨1, by decide⟩
def cB : Circuit 2 := Circuit.ofGates [Gate.cx j0 j1 (by decide), Gate.cx j0 j1 (by decide)]
#eval (quantumRules cB).length
#eval (oneStepRewrites cB).length
