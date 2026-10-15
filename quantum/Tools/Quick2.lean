import Quantum.Optimizer
open Quantum Quantum.Opt Quantum.EG LambdaSat UnionFind
set_option maxHeartbeats 4000000000
set_option maxRecDepth 100000
def i0 : Fin 1 := ⟨0, by decide⟩
def cA : Circuit 1 := Circuit.seq (Circuit.gate (Gate.h i0)) (Circuit.gate (Gate.h i0))

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println "start"
  let (root, g) := ofCircuit cA
  let t1 ← IO.monoMsNow
  IO.println s! "ofCircuit ok {t1 - t0}ms root {root} classes {g.numClasses}"
  let rs := (quantumRules cA).map fun psr => psr.rule
  let t2 ← IO.monoMsNow
  IO.println s! "rules {rs.length} ok {t2 - t1}ms"
  let gSat := saturateF 300 6 300 g rs
  let t3 ← IO.monoMsNow
  IO.println s! "saturate ok {t3 - t2}ms classes {gSat.numClasses}"
  let gCost := computeCostsF gSat egCostFn 60
  let t4 ← IO.monoMsNow
  IO.println s! "costs ok {t4 - t3}ms"
  let ex : Option (Circuit 1) := extractAuto gCost root
  let t5 ← IO.monoMsNow
  IO.println s! "extract ok {t5 - t4}ms -> {match ex with | none => "none" | some c' => toString c'.gates.length}"
  let r := optimize Config.default cA
  let t6 ← IO.monoMsNow
  IO.println s! "optimize ok {t6 - t5}ms -> {match r with | none => "none" | some (c', cert) => toString (c'.gates.length, cert.length, checkCertificate cA c' cert)}"
