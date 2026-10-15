import Quantum
import Shor

open Quantum Quantum.Opt Quantum.EG LambdaSat

namespace QuantumReview

def q : Fin 1 := 0
def z : Circuit 1 := .gate (.z q)
def x : Circuit 1 := .gate (.x q)
def h : Circuit 1 := .gate (.h q)
def nested : Circuit 1 := .seq z (.seq x (.seq h h))
def expected : Circuit 1 := .seq z (.seq x .one)
def validStep : Step 1 :=
  { ruleId := "hh", args := [.q q], ctx := .seqL z (.seqL x .hole), backward := false }

-- A valid rewrite is missing from the optimizer's advertised enumeration.
example : applyStep nested validStep = some expected := by decide
example : ((oneStepRewrites nested).any fun p => p.2 == expected) = false := by decide

-- This is the full conclusion of extraction_value_initial, with its extraction
-- hypothesis removed. The valuation is unconstrained, so the claim is automatic.
theorem extractionConclusionWithoutExtraction (cfg : Config) (c c' : Circuit n)
    (env : Nat → PhaseOp n) :
    ∃ (v_sat : EClassId → PhaseOp n), EvalExpr.evalExpr c' env =
      v_sat (UnionFind.root (saturateF cfg.fuel cfg.maxIter cfg.rebuildFuel (ofCircuit c).2
        ((quantumRules c).map fun psr => psr.rule)).unionFind (rootOf cfg c)) := by
  exact ⟨fun _ => EvalExpr.evalExpr c' env, rfl⟩

-- The claimed Clifford-only target accepts the non-Clifford pi/4 Z rotation.
example : Architecture.supports Architecture.clifford
    (.gate (.rz q (Angle.piMul (1 / 4))) : Circuit 1) = true := by decide

def onlyRz : Architecture :=
  { toffoliEquiv := fun _ => 0, supported := fun k => k == .rz }
example : Architecture.supports onlyRz (.gate (.rz q Angle.pi) : Circuit 1) = true := by decide
example : Architecture.supports onlyRz z = false := by decide
example : checkCertificate (.gate (.rz q Angle.pi) : Circuit 1) z
    [{ ruleId := "rz_pi_z", args := [.q q], ctx := .hole, backward := false }] = true := by decide

-- The selected "completeness" theorem asks for reconstruction to succeed even
-- with a malformed child list. This fails in this domain.
example : (Extractable.reconstruct (QOp.seq (n := 1) 0 1) ([] : List (Circuit 1))).isSome
    = false := by decide

-- A Fourier sample for secret k=5 under the documented f(a,b)=aP+bQ
-- convention satisfies d=k*c. Applying the module's purported measured-pair
-- formula to c=1,d=5 instead returns 4.
example : (5 : ZMod 7) = 5 * 1 := by decide
example : (3 : ZMod 7) * 5 = 1 := by decide
example : -(1 : ZMod 7) * 3 = 4 := by decide
example : ¬ ((1 : ZMod 7) + 5 * 5 = 0) := by decide

-- A resource "saving" on the sample starts from blocks already dropped by
-- cblock false, so the source and specialized circuit already have equal costs.
example : (Cost.of ladder).gateCount = (Cost.of ladderSpec).gateCount := by decide
example : toffoliT ladder = toffoliT ladderSpec := by decide

-- Equality of counts with no matching fuel is only a bounded observation,
-- not a fixed point of the available rewrite theory.
def zeroFuelReportsFixed : Bool :=
  saturationStatus { Config.default with fuel := 0, maxIter := 0 }
    (.seq h h) == .fixedPoint

-- The final semantic gate accepts a valid expansion as well as a contraction.
-- This is not a counterexample to optimize; it exhibits the scope of finish_spec.
def expansion : Step 1 :=
  { ruleId := "hh", args := [.q q], ctx := .hole, backward := true }
example : (finish (.one : Circuit 1) (.seq h h) [expansion]).1 = .seq h h := by decide

-- Constant propagation changes syntax, but the already evaluated source cost
-- is exactly the target cost, not only an upper bound.
theorem constPropCostEquality (l : List (Bool × Circuit n)) :
    (Cost.of (exec (constProp l))).gateCount = (Cost.of (condBlocks l)).gateCount := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨b, c⟩
    cases b <;> simp [exec, constProp, condBlocks, cblock, Cost.of, ih]

def main : IO Unit := do
  IO.println s!"valid nested HH checker step: {(applyStep nested validStep).isSome}"
  IO.println s!"enumerator reaches expected nested HH result: {(oneStepRewrites nested).any fun p => p.2 == expected}"
  IO.println s!"Clifford target accepts Rz(pi/4): {Architecture.supports Architecture.clifford (.gate (.rz q (Angle.piMul (1 / 4))) : Circuit 1)}"
  IO.println s!"zero matching fuel reports fixedPoint on HH: {zeroFuelReportsFixed}"

end QuantumReview

def main : IO Unit := QuantumReview.main
