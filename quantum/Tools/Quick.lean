import Quantum.Optimizer
open Quantum Quantum.Opt
set_option maxHeartbeats 4000000000
set_option maxRecDepth 100000
def i0 : Fin 1 := ⟨0, by decide⟩
def cA : Circuit 1 := Circuit.seq (Circuit.gate (Gate.h i0)) (Circuit.gate (Gate.h i0))
#eval (oneStepRewrites cA).length
#eval (quantumRules cA).length
#eval (Cost.of cA).gateCount
