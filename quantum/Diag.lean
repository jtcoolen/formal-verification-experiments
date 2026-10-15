/-
Pipeline diagnostics: where does the optimizer lose the optimum?

For each example circuit this prints the number of generated rule instances, the e-graph size
before and after saturation, the extracted circuit and its cost, and whether the certificate
search succeeds.  Compiled (lake exe diag) so the numbers are meaningful.
-/
import Quantum

open Quantum Quantum.Opt Quantum.EG LambdaSat

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 100000 in

def i0 : Fin 1 := ⟨0, by decide⟩
def j0 : Fin 2 := ⟨0, by decide⟩
def j1 : Fin 2 := ⟨1, by decide⟩
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

def sg : List (Gate n) -> Circuit n
  | [] => Circuit.one
  | [g] => Circuit.gate g
  | g :: gs => Circuit.seq (Circuit.gate g) (sg gs)

def diag {n : Nat} (label : String) (c : Circuit n) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (root, g) := ofCircuit c
  let rs := quantumRules c
  let t1 ← IO.monoMsNow
  IO.println s! "{label}: input gates={(Cost.of c).gateCount}, rules={rs.length}, classes0={g.numClasses} ({t1-t0} ms)"
  let gSat := saturateF 300 6 300 g (rs.map fun psr => psr.rule)
  let t2 ← IO.monoMsNow
  IO.println s! "  saturated: classes={gSat.numClasses} ({t2-t1} ms)"
  let gCost := computeCostsF gSat egCostFn 60
  let ex : Option (Circuit n) := extractAuto gCost root
  let t3 ← IO.monoMsNow
  match ex with
  | none => IO.println s! "  extraction: none ({t3-t2} ms)"
  | some c' =>
      IO.println s! "  extracted gates={(Cost.of c').gateCount} ({t3-t2} ms)"
      let der := findDerivation 8 c' 4000 [(c, [])] []
      let t4 ← IO.monoMsNow
      match der with
      | none => IO.println s! "  derivation search: FAILED ({t4-t3} ms)"
      | some cert =>
          IO.println s! "  derivation search: {cert.length} steps, accepted={checkCertificate c c' cert} ({t4-t3} ms)"

def main : IO Unit := do
  diag "E  TTTTSS " (sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0, Gate.s i0, Gate.s i0] : Circuit 1)
  diag "F  XZXZ   " (sg [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0] : Circuit 1)
  diag "I  CX X CX" (sg [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)] : Circuit 3)
  diag "H  TTTT   " (sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0] : Circuit 1)
  diag "D  X(0)Z(1)" (sg [Gate.x j0, Gate.z j1] : Circuit 2)
