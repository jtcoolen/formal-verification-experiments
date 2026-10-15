import Quantum.Optimizer
open Quantum Quantum.Opt Quantum.EG LambdaSat
set_option maxHeartbeats 4000000000
set_option maxRecDepth 100000
def i0 : Fin 1 := ⟨0, by decide⟩
def big : Angle := ⟨100000000000000000, 0⟩
def c1 : Circuit 1 := Circuit.seq (Circuit.gate (Gate.rz i0 big)) (Circuit.seq (Circuit.gate (Gate.rz i0 Angle.pi)) (Circuit.gate (Gate.rz i0 (-big))))
def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let (root, g) := ofCircuit c1
  let t1 ← IO.monoMsNow
  IO.println s! "ofCircuit {t1-t0}ms"
  let rs := (quantumRules c1).map fun psr => psr.rule
  let t2 ← IO.monoMsNow
  IO.println s! "rules {rs.length} {t2-t1}ms"
  let gSat := saturateF 300 6 300 g rs
  let t3 ← IO.monoMsNow
  IO.println s! "saturate {t3-t2}ms classes {gSat.numClasses}"
  let gCost := computeCostsF gSat egCostFn 60
  let t4 ← IO.monoMsNow
  IO.println s! "costs {t4-t3}ms"
  let ex : Option (Circuit 1) := extractAuto gCost root
  let t5 ← IO.monoMsNow
  IO.println s! "extract {t5-t4}ms -> {match ex with | none => "none" | some c => toString c.gates.length}"
  let os := oneStepRewrites c1
  let t6 ← IO.monoMsNow
  IO.println s! "oneStep {t6-t5}ms -> {os.length}"
