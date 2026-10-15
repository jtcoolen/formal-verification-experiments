import Quantum.Optimizer
open Quantum Quantum.Opt
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
def i0 : Fin 1 := ⟨0, by decide⟩
def cA : Circuit 1 := Circuit.ofGates [Gate.h i0, Gate.h i0]
#eval (quantumRules cA).length
#eval (oneStepRewrites cA).length
#eval (Cost.of cA).gateCount
