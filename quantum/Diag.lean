/-
Stage diagnostics for the optimizer pipeline, selected by command-line argument:
  diag iso             rule-set isolation experiment
  diag sat [f i r]     saturation only
  diag extract [f i r] saturation + extraction
  diag all  [f i r]    saturation + extraction + certificate searches
-/
import Quantum
import Shor

open Quantum Quantum.Opt Quantum.EG LambdaSat

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 100000 in

def trace (m : String) : IO Unit :=
  IO.FS.withFile "/tmp/diag_trace.txt" IO.FS.Mode.append fun h => h.putStrLn m

def i0 : Fin 1 := ⟨0, by decide⟩
def jj0 : Fin 2 := ⟨0, by decide⟩
def jj1 : Fin 2 := ⟨1, by decide⟩
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

def sg : List (Gate n) -> Circuit n
  | [] => Circuit.one
  | [g] => Circuit.gate g
  | g :: gs => Circuit.seq (Circuit.gate g) (sg gs)

def cF : Circuit 1 := sg [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]
def cE : Circuit 1 := sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0, Gate.s i0, Gate.s i0]
def cI : Circuit 3 :=
  sg [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)]

def natOr (o : Option String) (dflt : Nat) : Nat :=
  match o with
  | some t => match t.toNat? with
    | some n => n
    | none => dflt
  | none => dflt

def cfg6 : Config := { Config.default with maxSteps := 6, searchBudget := 300 }

def describeCert {n : Nat} (o : Option (Certificate n)) : String :=
  match o with
  | some cert => toString cert.length ++ " steps"
  | none => "FAILED"

/-- Which rule instances does the engine generate, and which family makes saturation blow up? -/
def iso {n : Nat} (label : String) (c : Circuit n) : IO Unit := do
  let (_root, g) := ofCircuit c
  let all := quantumRules c
  trace (label ++ " rules: " ++ (all.map fun r => r.rule.name).toString)
  let sids := (structRules n).map fun r => r.rule.name
  let gates := all.filter fun r => !sids.contains r.rule.name
  let sets : List (String × List (PatternSoundRule (QOp n) (PhaseOp n))) :=
    [("gates", gates), ("struct", structRules n), ("all", all)]
  for pair in sets do
    let t0 ← IO.monoMsNow
    let gs := saturateF 5 2 10 g (pair.2.map fun psr => psr.rule)
    let t1 ← IO.monoMsNow
    trace ("  " ++ pair.1 ++ ": classes=" ++ toString gs.numClasses ++ " (" ++ toString (t1-t0) ++ " ms)")

def one {n : Nat} (f it rf : Nat) (label : String) (c : Circuit n) (mode : String) : IO Unit := do
  trace (label ++ ": alphabet=" ++ toString ((kindClosure c).length) ++ " rules=" ++ toString ((quantumRules c).length))
  trace (label ++ ": names " ++ toString ((quantumRules c).map fun r => r.rule.name))
  let (root, g0) := ofCircuit c
  let t0 ← IO.monoMsNow
  let gSat := saturateF f it rf g0 ((quantumRules c).map fun psr => psr.rule)
  let t1 ← IO.monoMsNow
  trace (label ++ ": saturated classes=" ++ toString gSat.numClasses ++ " (" ++ toString (t1-t0) ++ " ms)")
  if mode == "sat" then return ()
  let gCost := computeCostsF gSat egCostFn cfg6.costFuel
  let ex := (extractAuto gCost root : Option (Circuit n))
  match ex with
  | none => trace (label ++ ": extraction none")
  | some c' =>
      trace (label ++ ": extracted " ++ toString (Cost.of c').gateCount ++ "g [" ++ c'.show ++ "]")
      if mode == "extract" then return ()
      let t2 ← IO.monoMsNow
      let r1 := costSearch cfg6 c' cfg6.searchBudget [(c, [])] []
      let t3 ← IO.monoMsNow
      trace (label ++ ": costSearch " ++ describeCert r1 ++ " (" ++ toString (t3-t2) ++ " ms)")
      let t4 ← IO.monoMsNow
      let r2 := findDerivationBidir 6 300 c c'
      let t5 ← IO.monoMsNow
      trace (label ++ ": bidir " ++ describeCert r2 ++ " (" ++ toString (t5-t4) ++ " ms)")

def main (args : List String) : IO Unit := do
  let mode := args.headD "all"
  let rest := args.drop 1
  let f := natOr (rest.drop 0 |>.head?) 60
  let it := natOr (rest.drop 1 |>.head?) 3
  let rf := natOr (rest.drop 2 |>.head?) 60
  trace ("=== MODE=" ++ mode ++ " fuel=" ++ toString f ++ " iter=" ++ toString it)
  if mode == "iso" then
    iso "F" cF
    iso "E" cE
    return ()
  if mode == "grow" then
    let (root, g0) := ofCircuit (n := 1) cF
    let rs := ((quantumRules (n := 1) cF).map fun psr => psr.rule).toArray
    for f in [1, 2, 3, 5] do
      for it in [1, 2] do
        let t0 ← IO.monoMsNow
        let gs := saturateF f it 5 g0 rs.toList
        let t1 ← IO.monoMsNow
        trace ("F fuel=" ++ toString f ++ " iter=" ++ toString it ++ ": classes=" ++ toString gs.numClasses ++ " (" ++ toString (t1-t0) ++ " ms)")
    let _ := root
    return ()
  one f it rf "F" cF mode
  one f it rf "E" cE mode
  one f it rf "I" cI mode
  one f it rf "S2" (sg [Gate.cp jj1 jj0 (by decide) (Angle.piMul (1 / 4)),
    Gate.cp jj1 jj0 (by decide) (Angle.piMul (1 / 4))] : Circuit 2) mode
  one f it rf "S1" (Circuit.seq Shor.QFT.qft2 Shor.QFT.iqft2 : Circuit 2) mode
