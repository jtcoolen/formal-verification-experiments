import Quantum.Optimizer
open Quantum Quantum.Opt
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
def i0 : Fin 1 := ⟨0, by decide⟩
def cF : Circuit 1 := Circuit.ofGates [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]
#eval (quantumRules cF).length
#eval (oneStepRewrites cF).length
