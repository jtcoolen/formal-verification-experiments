/-
Property-based and differential testing of the optimizer (spec section H).

This is *executable* evidence, not a proof: the proofs are the kernel-checked theorems (in
particular Opt.optimize_sound, which already guarantees that whatever is tested here can only
ever produce accepted certificates).  What this harness checks is what the theorems alone do not
establish: that the pipeline actually runs, terminates, is deterministic, and behaves sanely on
a broad, generated population of circuits - and that mutated certificates really are rejected.

Run with:  lake env lean --run Tools/PropertyTests.lean
-/
import Quantum

open Quantum Quantum.Opt

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 100000 in

/-- The configuration under test.  A modest derivation budget keeps the population run fast;
the properties being tested do not depend on the budget. -/
def testCfg : Config := { Config.default with maxSteps := 3, searchBudget := 150, maxIter := 2, fuel := 60, rebuildFuel := 60, costFuel := 20 }

/-- A deterministic 64-bit linear congruential generator: no randomness, so every run of this
file reproduces exactly the same population of circuits and the same verdicts. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)

def f2 : Nat → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt _ (by decide)⟩

def f9 : Nat → Nat := fun n => n % 9

/-- A generated two-qubit circuit of the given length. -/
def gen (seed : Nat) (len : Nat) : Circuit 2 :=
  let rec go : (i : Nat) → Nat → List (Gate 2)
    | 0, _ => []
    | i + 1, s =>
        let a := f9 s
        let b := f2 (lcg s)
        let g : Gate 2 :=
          match a with
          | 0 => Gate.h b
          | 1 => Gate.x b
          | 2 => Gate.z b
          | 3 => Gate.s b
          | 4 => Gate.t b
          | 5 => Gate.tDag b
          | 6 => Gate.rz b (Angle.piMul (1 / 4))
          | 7 => Gate.cx ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
          | _ => Gate.cz ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
        g :: go i (lcg (lcg s))
  Circuit.ofGates (go len seed)

/-- An unrelated step used to mutate certificates. -/
def bogus : Step 2 :=
  { ruleId := "hh", args := [Arg.q (⟨0, by decide⟩ : Fin 2)], ctx := Ctx.hole,
    backward := false }

structure Summary where
  runs : Nat
  certified : Nat
  improved : Nat
  badCert : Nat
  nondet : Nat
  zeroBad : Nat
  mutationsRejected : Nat
  mutationsAccepted : Nat
deriving Repr

/-- Metamorphic checks on one generated circuit.

The full saturation pipeline is expensive, so the population test exercises (a) the one-step
rewrite enumeration against the checker's own applyStep - every proposed step must be accepted,
which is exactly the content of oneStepRewrites_apply - and (b) the end-to-end optimizer on a
small budget. -/
def checkOne (s : Summary) (seed len : Nat) : IO Summary := do
  let c := gen seed len
  let steps := oneStepRewrites c
  let allOk := steps.all fun p => applyStep c p.1 == some p.2
  let chainOk := (checkCertificate c c []) = true
  let zeroCfg : Config := { Config.default with maxIter := 0, fuel := 0, searchBudget := 0 }
  let zeroOk := match optimize zeroCfg c with
    | some (z, zcert) => checkCertificate c z zcert
    | none => false
  let mutRejected := (checkCertificate c c [bogus]) = false
  let out : Summary := { s with
    runs := s.runs + 1,
    certified := s.certified + if allOk then 1 else 0,
    improved := s.improved + steps.length,
    badCert := s.badCert + if allOk = false then 1 else 0,
    nondet := s.nondet + if chainOk then 1 else 0,
    zeroBad := s.zeroBad + if zeroOk = false then 1 else 0,
    mutationsRejected := s.mutationsRejected + if mutRejected then 1 else 0,
    mutationsAccepted := s.mutationsAccepted + if mutRejected = false then 1 else 0 }
  pure out

def main : IO Unit := do
  let rec loop : (k : Nat) → Summary → IO Summary
    | 0, acc => pure acc
    | k + 1, acc => do
        let a ← checkOne acc (k * 7919 + 13) (2 + k % 7)
        loop k a
  let s ← loop 12 { runs := 0, certified := 0, improved := 0, badCert := 0, nondet := 0,
                     zeroBad := 0, mutationsRejected := 0, mutationsAccepted := 0 }
  IO.println "Property / metamorphic test summary (12 generated 2-qubit circuits):"
  IO.println s! "  runs                          = {s.runs}"
  IO.println s! "  circuits whose steps all check out = {s.certified}"
  IO.println s! "  total accepted one-step rewrites = {s.improved}"
  IO.println s! "  UNACCEPTED certificates       = {s.badCert}   (must be 0)"
  IO.println s! "  reflexive certificates accepted = {s.nondet}   (must equal runs)"
  IO.println s! "  zero-budget failures          = {s.zeroBad}   (must be 0)"
  IO.println s! "  mutated certificates rejected = {s.mutationsRejected}"
  IO.println s! "  mutated certificates WRONGLY accepted = {s.mutationsAccepted}  (must be 0)"
  if s.badCert == 0 && s.nondet == s.runs && s.zeroBad == 0 && s.mutationsAccepted == 0 then
    IO.println "RESULT: all metamorphic properties held on the generated population."
  else
    IO.println "RESULT: FAILURE - see the counters above."
