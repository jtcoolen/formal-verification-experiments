/-
The command-line demonstration.

Runs the equality-saturation optimizer on the required examples, prints the original and
optimized circuits with their costs, generates a certificate for each optimization, and
re-checks every certificate with the independent checker.

Nothing printed here is a proof: the proofs are the kernel-checked theorems in
Quantum/Examples.lean, Quantum/BugRegression.lean and Quantum/Correctness.lean, which
establish exactly the statements this program exhibits.

Usage: lake exe quantum            (all examples)
       lake exe quantum A          (only the example whose key is A)
-/
import Quantum
import Shor

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

def showG {n : Nat} : Gate n -> String
  | Gate.h _ => "H"
  | Gate.x _ => "X"
  | Gate.y _ => "Y"
  | Gate.z _ => "Z"
  | Gate.s _ => "S"
  | Gate.t _ => "T"
  | Gate.sDag _ => "S-dag"
  | Gate.tDag _ => "T-dag"
  | Gate.rz _ a => "Rz(" ++ toString a.rat ++ "+" ++ toString a.piQ ++ "pi)"
  | Gate.rx _ a => "Rx(" ++ toString a.rat ++ "+" ++ toString a.piQ ++ "pi)"
  | Gate.ry _ a => "Ry(" ++ toString a.rat ++ "+" ++ toString a.piQ ++ "pi)"
  | Gate.cx i j _ => "CX(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.cz i j _ => "CZ(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.swap i j _ => "SWAP(" ++ toString i.val ++ "," ++ toString j.val ++ ")"
  | Gate.cp i j _ a =>
      "CP(" ++ toString i.val ++ "," ++ toString j.val ++ "," ++ toString a.piQ ++ "pi)"
  | Gate.crz i j _ a =>
      "CRz(" ++ toString i.val ++ "," ++ toString j.val ++ "," ++ toString a.piQ ++ "pi)"

def showC {n : Nat} (c : Circuit n) : String :=
  String.intercalate " ; " (c.gates.map showG)

def showCost (c : Cost) : String :=
  "gates=" ++ toString c.gateCount ++ " 2q=" ++ toString c.twoQubitCount ++
  " T=" ++ toString c.tCount

/-- Optimize with cfg, re-check the certificate, and print everything. -/
def demoWith {n : Nat} (cfg : Config) (label : String) (c : Circuit n) : IO Unit := do
  IO.println (String.replicate 78 '=')
  IO.println label
  let ci := Cost.of c
  IO.println s! "  input : {showC c}   [{showCost ci}]"
  let t0 ← IO.monoMsNow
  match optimize cfg c with
  | none => IO.println "  optimizer returned no result (fail closed)"
  | some (c', cert) =>
      let t1 ← IO.monoMsNow
      let co := Cost.of c'
      let ok := checkCertificate c c' cert
      IO.println s! "  output: {showC c'}   [{showCost co}]"
      IO.println s! "  certificate: {cert.length} step(s); independent checker: "
      IO.println s! "    {if ok then "ACCEPTS" else "REJECTS"}   (search took {t1 - t0} ms)"
      for s in cert do
        IO.println s! "    step {s.ruleId}{if s.backward then " (backward)" else ""}"
      if !ok then
        IO.println "  !! REJECTED - the optimizer must not have returned this"

/-- Optimize with the default configuration. -/
def demo {n : Nat} (label : String) (c : Circuit n) : IO Unit :=
  demoWith Config.default label c

/-- Print a certificate that must be rejected by the independent checker. -/
def demoReject {n : Nat} (label : String) (a b : Circuit n) (cert : Certificate n) : IO Unit := do
  IO.println (String.replicate 78 '=')
  IO.println label
  if checkCertificate a b cert then
    IO.println "  independent checker: ACCEPTS (BAD!)"
  else
    IO.println "  independent checker: REJECTS (as required)"

/-- Run only the selected example (empty argument = run everything). -/
def only (sel key : String) : Bool := sel.isEmpty || sel == key

/-- A configuration for the rotation examples: instantiating the angle rules enlarges the
search space, so the derivation search is bounded more tightly. -/
def rotationConfig : Config := { Config.default with searchBudget := 800 }

/-- The configuration used by the live demonstration: a small derivation budget keeps the
command-line run fast.  The deeper certificates are the ones in Quantum/Examples.lean. -/
def fastConfig : Config := { Config.default with searchBudget := 400 }

/-- Show a certificate that is already in the library, together with the independent checker's
verdict and the theorem that turns the verdict into semantic equivalence.  This part of the
demonstration does no search at all: it is the *verification* side of the pipeline. -/
def showCert {n : Nat} (label : String) (a b : Circuit n) (cert : Certificate n) : IO Unit := do
  IO.println (String.replicate 78 '=')
  IO.println label
  IO.println s! "  from: {showC a}"
  IO.println s! "  to:   {showC b}"
  IO.println s! "  {cert.length} step(s); independent checker:     {if checkCertificate a b cert then "ACCEPTS" else "REJECTS"}"
  for s in cert do
    IO.println s! "    step {s.ruleId}{if s.backward then " (backward)" else ""}"

/-- The library certificates for the examples that need a deeper search than the live
optimizer is configured for here; each one is a kernel-checked theorem in Quantum/Examples. -/
def libraryCerts : IO Unit := do
  showCert "Example E (certificate from Quantum/Examples.lean, theorem Examples.checkE)"
    Examples.cE Circuit.one Examples.certE
  showCert "Example F/G (Examples.checkFG): X Z X Z -> identity, via a cost-neutral step"
    Examples.cFG Circuit.one Examples.certFG
  showCert "Example H (Examples.checkH): T T T T -> Z, T-count 4 -> 0"
    Examples.cH Examples.dH Examples.certH
  showCert "Example I (Examples.checkI): CNOT X CNOT -> X, two-qubit count 2 -> 0"
    Examples.cI Examples.dI Examples.certI
  showCert "Example J (Examples.checkJ): compute ; uncompute -> identity (exactly)"
    Examples.cJ Circuit.one Examples.certJ


/-- Constant propagation on a classically-controlled ladder (arXiv:2609.09582 section 5.3.6). -/
def demoSpecialize : IO Unit := do
  let sg := staticGateCount (bits13.zip blocks13)
  let st := staticToffoli Architecture.default (bits13.zip blocks13)
  let ag := (Cost.of ladderSpec).gateCount
  let ato := toffoliT ladderSpec
  IO.println (String.replicate 78 '=')
  IO.println "Pass: classical-control constant propagation (exact specialization)"
  IO.println ("  guarded ladder   : " ++ showC ladder)
  IO.println ("    static cost: gates=" ++ toString sg ++ "  Toffoli=" ++ toString st)
  IO.println ("  after propagation: " ++ showC ladderSpec)
  IO.println ("    specialized cost: gates=" ++ toString ag ++ "  Toffoli=" ++ toString ato)
  IO.println "  both circuits denote the SAME unitary (theorem ladder_exact)"

/-- Shor's algorithm: the classically verified post-processing. -/
def demoShor : IO Unit := do
  IO.println (String.replicate 78 '=')
  IO.println "Shor: order-finding post-processing (theorems Shor.factor_15, Shor.factor_21)"
  IO.println ("  order of 2 mod 15 = " ++ toString (Shor.order 2 15) ++ ";  y = 2^(order/2) = 4")
  IO.println ("  gcd(y-1, 15) = " ++ toString (Nat.gcd (4 - 1) 15) ++ "  ->  15 = 3 * 5")
  IO.println ("  order of 2 mod 21 = " ++ toString (Shor.order 2 21) ++ ";  y = 2^(order/2) = 8")
  IO.println ("  gcd(y-1, 21) = " ++ toString (Nat.gcd (8 - 1) 21) ++ "  ->  21 = 3 * 7")
  IO.println "  RSA n = 33 = 3*11, e = 3, d = 7:"
  IO.println "    decrypt(encrypt m) = m for every one of the 33 messages (Shor.rsa_roundtrip_33)"
  IO.println "  ECDLP recovery: r = 7, measured (c,d) = (6,3) gives k = 5 (Shor.ECDLP.recovered_7)"

def main (args : List String) : IO Unit := do
  let sel := args.headD ""
  IO.println "Proof-producing quantum circuit optimizer (Lean 4 + Mathlib + OptiSat)"
  IO.println "Every optimization below is justified by a certificate that the INDEPENDENT"
  IO.println "checker (Quantum/Certificates.lean) re-verifies step by step."
  if only sel "L" || only sel "" then libraryCerts
  if only sel "A" then
    demoWith fastConfig "Example A: H(0) ; H(0)  ->  identity" (sg [Gate.h i0, Gate.h i0] : Circuit 1)
  if only sel "B" then
    demoWith fastConfig "Example B: CNOT(0,1) ; CNOT(0,1)  ->  identity"
      (sg [Gate.cx j0 j1 (by decide), Gate.cx j0 j1 (by decide)] : Circuit 2)
  if only sel "C1" then
    demoWith fastConfig "Example C1: S(0) ; S(0)  ->  Z(0)" (sg [Gate.s i0, Gate.s i0] : Circuit 1)
  if only sel "C2" then
    demoWith fastConfig "Example C2: T(0) ; T(0)  ->  S(0)" (sg [Gate.t i0, Gate.t i0] : Circuit 1)
  if only sel "D" then
    demoWith fastConfig "Example D: X(0) ; Z(1)  <->  Z(1) ; X(0) (cost-neutral commutation)"
      (sg [Gate.x j0, Gate.z j1] : Circuit 2)
  if only sel "E" then
    demoWith fastConfig
      "Example E: T T T T S S  ->  Z ; Z  (multi-step: tt, ss, re-bracketing; T-count 4 -> 0)"
      (sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0, Gate.s i0, Gate.s i0] : Circuit 1)
  if only sel "F" then
    demoWith fastConfig
      "Example F: X Z X Z  ->  X ; X  (engine; the cost-neutral step is the XZ <-> ZX commutation)"
      (sg [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0] : Circuit 1)
  if only sel "H" then
    demoWith fastConfig "Example H: T T T T  ->  Z (T-count 4 -> 0)"
      (sg [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0] : Circuit 1)
  if only sel "I" then
    demoWith fastConfig "Example I: CNOT(0,1) ; X(2) ; CNOT(0,1)  ->  X(2) (two-qubit count 2 -> 0)"
      (sg [Gate.cx k0 k1 (by decide), Gate.x k2, Gate.cx k0 k1 (by decide)] : Circuit 3)
  if only sel "J" then
    let work := sg [Gate.h j0, Gate.cx j0 j1 (by decide), Gate.s j1]
    demoWith fastConfig "Example J: a block followed by its own uncomputation  ->  identity"
      (Circuit.seq work (Circuit.inv work) : Circuit 2)
  if only sel "K" && !sel.isEmpty then
    let big : Angle := ⟨100000000000000000, 0⟩
    demoWith rotationConfig
      "Bug regression 1: Rz(10^17) ; Rz(pi) ; Rz(-10^17)  =  Rz(pi), NOT identity"
      (sg [Gate.rz i0 big, Gate.rz i0 Angle.pi, Gate.rz i0 (-big)] : Circuit 1)
  if only sel "P" then demoSpecialize
  if only sel "R" then demoShor
  if only sel "N" then
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
      Examples.cFG (Circuit.one : Circuit 1) Examples.certFG.reverse
    demoReject "Negative test: CNOT control/target exchanged in the output"
      (sg [Gate.cx j0 j1 (by decide)] : Circuit 2) (sg [Gate.cx j1 j0 (by decide)] : Circuit 2)
      [Examples.fwd "cxcx" [Arg.q j0, Arg.q j1] Ctx.hole]
  IO.println (String.replicate 78 '=')
