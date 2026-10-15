/-
The command-line demonstration.

Runs the equality-saturation optimizer on the required examples, prints the original and
optimized circuits with their costs, generates a certificate for each optimization, and
re-checks every certificate with the independent checker.  Nothing printed here is a proof:
the proofs are the `decide`-checked theorems in Quantum/Examples.lean and
Quantum/BugRegression.lean, which establish exactly the statements printed below.
-/
import Quantum

open Quantum Quantum.Opt

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

/-- Show a gate as text. -/
def showG {n : Nat} : Gate n -> String
  | Gate.h _ => "H"
  | Gate.x _ => "X"
  | Gate.y _ => "Y"
  | Gate.z _ => "Z"
  | Gate.s _ => "S"
  | Gate.t _ => "T"
  | Gate.sDag _ => "S\u{2020}"
  | Gate.tDag _ => "T\u{2020}"
  | Gate.rz _ a => "Rz(" ++ toString a.piQ ++ "pi+" ++ toString a.rat ++ ")"
  | Gate.rx _ a => "Rx(" ++ toString a.piQ ++ "pi+" ++ toString a.rat ++ ")"
  | Gate.ry _ a => "Ry(" ++ toString a.piQ ++ "pi+" ++ toString a.rat ++ ")"
  | Gate.cx i j _ => "CX(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.cz i j _ => "CZ(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.swap i j _ => "SWAP(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.crz i j _ a =>
      "CRz(" ++ toString i.val ++ "," ++ toString j.val ++ "," ++ toString a.piQ ++ "pi)"

def showC {n : Nat} (c : Circuit n) : String :=
  String.intercalate " ; " (c.gates.map showG)

def showCost (c : Cost) : String :=
  "gates=" ++ toString c.gateCount ++ " 2q=" ++ toString c.twoQubitCount ++
  " T=" ++ toString c.tCount

/-- Optimize, re-check the certificate, and print everything. -/
def demo {n : Nat} (label : String) (c : Circuit n) : IO Unit := do
  IO.println ("=" ++ String.replicate 74 "=")
  IO.println s! "{label}"
  IO.println s! "  input : {showC c}   [{showCost (Cost.of c)}]"
  match optimize Config.default c with
  | none => IO.println "  optimizer returned no result (fail closed)"
  | some (c', cert) =>
      let ok := checkCertificate c c' cert
      IO.println s! "  output: {showC c'}   [{showCost (Cost.of c')}]"
      IO.println s! "  certificate: {cert.length} step(s); independent checker: {if ok then "ACCEPTS" else "REJECTS"}"
      for (s : Step n) in cert do
        IO.println s! "    step {s.ruleId}{if s.backward then " (backward)" else ""}"
      if !ok then IO.println "  !! REJECTED - the optimizer must not have returned this" else pure ()

/-- Print a certificate that must be *rejected*. -/
def demoReject {n : Nat} (label : String) (a b : Circuit n) (cert : Certificate n) : IO Unit := do
  IO.println ("=" ++ String.replicate 74 "=")
  IO.println s! "{label}"
  IO.println s! "  independent checker: {if checkCertificate a b cert then "ACCEPTS (BAD!)" else "REJECTS (as required)"}"

def main : IO Unit := do
  IO.println "Proof-producing quantum circuit optimizer (Lean 4 + Mathlib + OptiSat)";
  IO.println "Every optimization below is justified by a certificate re-checked by the";
  IO.println "independent checker in Quantum/Certificates.lean.";
  demo "Example A: H(0) ; H(0)  ->  identity"
    (sg [Gate.h i0, Gate.h i0] : Circuit 1)
  demo "Example B: CNOT(0,1) ; CNOT(0,1)  ->  identity"
    (sg [Gate.cx j0 j1 (by decide), Gate.cx j0 j1 (by decide)] : Circuit 2)
  demo "Example C1: S(0) ; S(0)  ->  Z(0)"
    (sg [Gate.s i0, Gate.s i0] : Circuit 1)
  demo "Example C2: T(0) ; T(0)  ->  S(0)"
    (sg [Gate.t i0, Gate.t i0] : Circuit 1)
  demo "Example D: X(0) ; Z(1)  <->  Z(1) ; X(0) (cost-neutral commutation)"
    (sg [Gate.x j0, Gate.z j1] : Circuit 2)
  demo "Example E: T T T T S S  ->  identity (multi-step)"
    (sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0, Gate.s i0, Gate.s i0] : Circuit 1)
  demo "Example F/G: X Z X Z  ->  identity (needs a cost-neutral step)"
    (sg [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0] : Circuit 1)
  demo "Example H: T T T T  ->  Z (T-count 4 -> 0)"
    (sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0] : Circuit 1)
  demo "Example I: CNOT(0,1) ; X(2) ; CNOT(0,1)  ->  X(2) (two-qubit count 2 -> 0)"
    (sg [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)] : Circuit 3)
  demo "Example J: a block followed by its uncomputation  ->  identity"
    (Circuit.seq (sg [Gate.h j0, Gate.cx j0 j1 (by decide), Gate.s j1])
      (Circuit.inv (sg [Gate.h j0, Gate.cx j0 j1 (by decide), Gate.s j1])) : Circuit 2)
  demo "Bug regression 1: Rz(10^17) ; Rz(pi) ; Rz(-10^17)  =  Rz(pi), NOT identity"
    (sg [Gate.rz i0 ⟨100000000000000000, 0⟩, Gate.rz i0 ⟨0, 1⟩, Gate.rz i0 ⟨-100000000000000000, 0⟩] : Circuit 1)
  demo "Bug regression 2: QuiZX overflow pair, exact rational phases"
    (sg [Gate.rz i0 ⟨0, Rat.mk 2147483647 4294967295⟩,
         Gate.rz i0 ⟨0, Rat.mk 2147483648 4294967297⟩] : Circuit 1)
  demoReject "Negative test: wrong final circuit"
    (sg [Gate.h i0, Gate.h i0] : Circuit 1) (sg [Gate.h i0] : Circuit 1)
    [Examples.fwd "hh" [Arg.q i0] Ctx.hole]
  demoReject "Negative test: unknown rule id"
    (sg [Gate.h i0, Gate.h i0] : Circuit 1) (Circuit.one : Circuit 1)
    [{ ruleId := "not-a-rule", args := [Arg.q i0], ctx := Ctx.hole, backward := false }]
  demoReject "Negative test: wrong qubit index in the rule instantiation"
    (sg [Gate.h j0, Gate.h j0] : Circuit 2) (Circuit.one : Circuit 2)
    [Examples.fwd "hh" [Arg.q j1] Ctx.hole]
  demoReject "Negative test: tampered (reversed) derivation order"
    Examples.cE (Circuit.one : Circuit 1) (Examples.certE.reverse)
  IO.println ("=" ++ String.replicate 74 "=")
