/-
Certificate generator / printer (development tool, not part of the library).

Runs the bounded equality-saturation optimizer on the example circuits and prints the
resulting certificates as Lean source text, so that Quantum/Examples.lean can contain
explicit, human-readable derivations that the independent checker accepts.
-/
import Quantum.Optimizer

open Quantum Quantum.Opt

set_option maxHeartbeats 4000000000
set_option maxRecDepth 100000

def showFin {n : Nat} (i : Fin n) : String :=
  "(⟨" ++ toString i.val ++ ", by decide⟩ : Fin " ++ toString n ++ ")"

def showAngle (a : Angle) : String := "⟨" ++ toString a.rat ++ ", " ++ toString a.piQ ++ "⟩"

def showGate {n : Nat} : Gate n -> String
  | Gate.h i => "Gate.h " ++ showFin i
  | Gate.x i => "Gate.x " ++ showFin i
  | Gate.y i => "Gate.y " ++ showFin i
  | Gate.z i => "Gate.z " ++ showFin i
  | Gate.s i => "Gate.s " ++ showFin i
  | Gate.t i => "Gate.t " ++ showFin i
  | Gate.sDag i => "Gate.sDag " ++ showFin i
  | Gate.tDag i => "Gate.tDag " ++ showFin i
  | Gate.rz i a => "Gate.rz " ++ showFin i ++ " (" ++ showAngle a ++ ")"
  | Gate.rx i a => "Gate.rx " ++ showFin i ++ " (" ++ showAngle a ++ ")"
  | Gate.ry i a => "Gate.ry " ++ showFin i ++ " (" ++ showAngle a ++ ")"
  | Gate.cx i j _ => "Gate.cx " ++ showFin i ++ " " ++ showFin j ++ " (by decide)"
  | Gate.cz i j _ => "Gate.cz " ++ showFin i ++ " " ++ showFin j ++ " (by decide)"
  | Gate.swap i j _ => "Gate.swap " ++ showFin i ++ " " ++ showFin j ++ " (by decide)"
  | Gate.crz i j _ a =>
      "Gate.crz " ++ showFin i ++ " " ++ showFin j ++ " (by decide) (" ++ showAngle a ++ ")"

def showCircuit {n : Nat} : Circuit n -> String
  | Circuit.one => "Circuit.one"
  | Circuit.gate g => "(Circuit.gate " ++ showGate g ++ ")"
  | Circuit.seq a b => "(Circuit.seq " ++ showCircuit a ++ " " ++ showCircuit b ++ ")"

def showArg {n : Nat} : Arg n -> String
  | Arg.q i => "Arg.q " ++ showFin i
  | Arg.a x => "Arg.a " ++ showAngle x
  | Arg.g g => "Arg.g " ++ showGate g
  | Arg.c c => "Arg.c " ++ showCircuit c

def showCtx {n : Nat} : Ctx n -> String
  | Ctx.hole => "Ctx.hole"
  | Ctx.seqL d k => "(Ctx.seqL " ++ showCircuit d ++ " " ++ showCtx k ++ ")"
  | Ctx.seqR k d => "(Ctx.seqR " ++ showCtx k ++ " " ++ showCircuit d ++ ")"

def showStep {n : Nat} (s : Step n) : String :=
  "{ ruleId := " ++ toString s.ruleId ++ ", args := [" ++
  (String.intercalate ", " (s.args.map showArg)) ++ "], ctx := " ++
  showCtx s.ctx ++ ", backward := " ++ toString s.backward ++ " }"

def showCert {n : Nat} (cert : Certificate n) : String :=
  "[" ++ String.intercalate ",\n  " (cert.map showStep) ++ "]"

def dump (path : String) (s : String) : IO Unit :=
  IO.FS.withFile path IO.FS.Mode.write (fun h => h.putStrLn s)

def report {n : Nat} (label : String) (c : Circuit n) : IO Unit := do
  let ci := Cost.of c
  let msg : List String := [ "--- " ++ label,
    s! "-- input gates: {c.gates.length}, cost: ({ci.gateCount},{ci.twoQubitCount},{ci.tCount})" ]
  match optimize Config.default c with
  | none => dump ("/tmp/cert_" ++ label ++ ".txt") (String.intercalate "\n" (msg ++ ["none"]))
  | some (c', cert) =>
      let co := Cost.of c'
      let msg2 := msg ++
        [ s! "-- output gates: {c'.gates.length}, cost: ({co.gateCount},{co.twoQubitCount},{co.tCount})",
          s! "-- checked: {checkCertificate c c' cert}, steps: {cert.length}",
          "-- output circuit: " ++ showCircuit c',
          "def cert : Certificate _ :=", showCert cert ]
      dump ("/tmp/cert_" ++ label ++ ".txt") ((String.intercalate "\n" msg2) ++ "\n")

def i0 : Fin 1 := ⟨0, by decide⟩
def j0 : Fin 2 := ⟨0, by decide⟩
def j1 : Fin 2 := ⟨1, by decide⟩
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

/-- Right-nested circuit of a gate list, without a trailing identity. -/
def sg : List (Gate n) -> Circuit n
  | [] => Circuit.one
  | [g] => Circuit.gate g
  | g :: gs => Circuit.seq (Circuit.gate g) (sg gs)

def cA : Circuit 1 := sg [Gate.h i0, Gate.h i0]
def cB : Circuit 2 := sg [Gate.cx j0 j1 (by decide), Gate.cx j0 j1 (by decide)]
def cC1 : Circuit 1 := sg [Gate.s i0, Gate.s i0]
def cC2 : Circuit 1 := sg [Gate.t i0, Gate.t i0]
def cD : Circuit 2 := sg [Gate.x j0, Gate.z j1]
def cE : Circuit 1 := sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0, Gate.s i0, Gate.s i0]
def cFG : Circuit 1 := sg [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]
def cH : Circuit 1 := sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0]
def cI : Circuit 3 := sg [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)]
def cJ : Circuit 2 := sg [Gate.rz j0 ⟨0, 0⟩, Gate.h j0]

def main : IO Unit := do
  report "A" cA
  report "B" cB
  report "C1" cC1
  report "C2" cC2
  report "D" cD
  report "E" cE
  report "FG" cFG
  report "H" cH
  report "I" cI
  report "J" cJ
  IO.println "all done"
