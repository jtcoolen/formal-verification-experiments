/-
Executable, machine-checked examples.

For every example we give
  * the input circuit,
  * the optimized circuit,
  * an explicit derivation certificate,
  * an executable check that the independent certificate checker accepts it, and
  * a Lean theorem deriving PhaseEquivalent from the accepted certificate.

The certificates are *not* produced by trusting the optimizer: each one is checked step by
step by Quantum/Certificates.lean, and the theorems below are instances of the checker
soundness theorem (checkCertificate_sound).  The optimizer itself is exercised on the same
circuits in Main.lean and in Quantum/BugRegression.lean.
-/
import Quantum.Optimizer
import Quantum.ControlPhase

namespace Quantum
namespace Examples

open Classical

def i0 : Fin 1 := ⟨0, by decide⟩
def j0 : Fin 2 := ⟨0, by decide⟩
def j1 : Fin 2 := ⟨1, by decide⟩
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

def cx2 : Gate 2 := Gate.cx j0 j1 (by decide)
def cx3 : Gate 3 := Gate.cx k0 k1 (by decide)

/-- A forward certificate step. -/
def fwd {n : Nat} (name : String) (args : List (Arg n)) (ctx : Ctx n) : Step n :=
  { ruleId := name, args := args, ctx := ctx, backward := false }

/-- A backward certificate step (rule applied right-to-left). -/
def bwd {n : Nat} (name : String) (args : List (Arg n)) (ctx : Ctx n) : Step n :=
  { ruleId := name, args := args, ctx := ctx, backward := true }

/-- The circuit that applies a list of gates in order (right-nested, no trailing identity). -/
def seqGates : List (Gate n) -> Circuit n
  | [] => Circuit.one
  | [g] => Circuit.gate g
  | g :: gs => Circuit.seq (Circuit.gate g) (seqGates gs)

/-- Extend a context so that the hole sits *after* the gate `g` (which executes first). -/
def afterG {n : Nat} (g : Gate n) : Ctx n -> Ctx n := fun k => Ctx.seqL (Circuit.gate g) k

/-- Extend a context so that the hole sits *before* the gate `g` (which executes after the
hole). -/
def beforeG {n : Nat} (g : Gate n) : Ctx n -> Ctx n := fun k => Ctx.seqR k (Circuit.gate g)

/-- Put a whole circuit after the hole. -/
def beforeC {n : Nat} (d : Circuit n) : Ctx n -> Ctx n := fun k => Ctx.seqR k d

/-! ### Example A: double Hadamard -/

/-- H(0) ; H(0) -/
def cA : Circuit 1 := seqGates [Gate.h i0, Gate.h i0]
/-- The certificate: cancel the two Hadamards. -/
def certA : Certificate 1 := [fwd "hh" [Arg.q i0] Ctx.hole]

theorem checkA : checkCertificate cA Circuit.one certA = true := by decide
theorem soundA : PhaseEquivalent cA Circuit.one :=
  checkCertificate_sound cA Circuit.one certA checkA
theorem costA : (Cost.of cA).gateCount = 2 := by decide
theorem costA' : (Cost.of (Circuit.one : Circuit 1)).gateCount = 0 := by decide

/-! ### Example B: double CNOT -/

/-- CNOT(0,1) ; CNOT(0,1) -/
def cB : Circuit 2 := seqGates [cx2, cx2]
def certB : Certificate 2 := [fwd "cxcx" [Arg.q j0, Arg.q j1] Ctx.hole]

theorem checkB : checkCertificate cB Circuit.one certB = true := by decide
theorem soundB : PhaseEquivalent cB Circuit.one :=
  checkCertificate_sound cB Circuit.one certB checkB
theorem costB : (Cost.of cB).twoQubitCount = 2 := by decide
theorem costB' : (Cost.of (Circuit.one : Circuit 2)).twoQubitCount = 0 := by decide

/-! ### Example C: phase simplification S;S = Z and T;T = S -/

def cC1 : Circuit 1 := seqGates [Gate.s i0, Gate.s i0]
def dC1 : Circuit 1 := Circuit.gate (Gate.z i0)
def certC1 : Certificate 1 := [fwd "ss" [Arg.q i0] Ctx.hole]
theorem checkC1 : checkCertificate cC1 dC1 certC1 = true := by decide
theorem soundC1 : PhaseEquivalent cC1 dC1 := checkCertificate_sound cC1 dC1 certC1 checkC1
theorem costC1 : (Cost.of cC1).gateCount = 2 ∧ (Cost.of dC1).gateCount = 1 := by decide

def cC2 : Circuit 1 := seqGates [Gate.t i0, Gate.t i0]
def dC2 : Circuit 1 := Circuit.gate (Gate.s i0)
def certC2 : Certificate 1 := [fwd "tt" [Arg.q i0] Ctx.hole]
theorem checkC2 : checkCertificate cC2 dC2 certC2 = true := by decide
theorem soundC2 : PhaseEquivalent cC2 dC2 := checkCertificate_sound cC2 dC2 certC2 checkC2
theorem tcountC2 : (Cost.of cC2).tCount = 2 ∧ (Cost.of dC2).tCount = 0 := by decide

/-! ### Example D: verified cost-neutral commutation on disjoint qubits -/

/-- X(0) ; Z(1) -/
def cD : Circuit 2 := seqGates [Gate.x j0, Gate.z j1]
/-- Z(1) ; X(0) -/
def dD : Circuit 2 := seqGates [Gate.z j1, Gate.x j0]
def certD : Certificate 2 := [fwd "disjoint" [Arg.g (Gate.x j0), Arg.g (Gate.z j1)] Ctx.hole]
theorem checkD : checkCertificate cD dD certD = true := by decide
theorem soundD : PhaseEquivalent cD dD := checkCertificate_sound cD dD certD checkD
theorem costD : Cost.of cD = Cost.of dD := by decide
/-- Disjoint gates commute *exactly*: no global phase is involved. -/
theorem exactD : EqExact cD dD := by
  show embed1 Z2 j1 * embed1 X2 j0 = embed1 X2 j0 * embed1 Z2 j1
  exact (embed1_embed1_comm (i := j0) (j := j1) (hij := by decide) X2 Z2).symm

/-! ### Example E: a multi-step optimization needing associativity -/

/-- T(0) ; T(0) ; T(0) ; T(0) ; S(0) ; S(0).  Four T gates are a Z and two S gates are a Z,
so the whole circuit is Z ; Z = I.  No single rewrite gets below five gates: the reduction
needs the phase-combination rules *and* re-association, because a right-nested circuit does
not contain the inner gate pairs as subterms. -/
def cE : Circuit 1 :=
  seqGates [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0, Gate.s i0, Gate.s i0]

def certE1 : Certificate 1 :=
  [ fwd "ss" [Arg.q i0] (afterG (Gate.t i0) (afterG (Gate.t i0)
        (afterG (Gate.t i0) (afterG (Gate.t i0) Ctx.hole)))),
    bwd "assoc" [Arg.c (Circuit.gate (Gate.t i0)), Arg.c (Circuit.gate (Gate.t i0)),
      Arg.c (seqGates [Gate.t i0, Gate.t i0, Gate.z i0])] Ctx.hole,
    fwd "tt" [Arg.q i0] (beforeC (seqGates [Gate.t i0, Gate.t i0, Gate.z i0]) Ctx.hole) ]

/-- The intermediate circuit after the three steps above: S ; T ; T ; Z. -/
def dE1 : Circuit 1 := seqGates [Gate.s i0, Gate.t i0, Gate.t i0, Gate.z i0]

theorem checkE1 : checkCertificate cE dE1 certE1 = true := by decide
theorem soundE1 : PhaseEquivalent cE dE1 := checkCertificate_sound cE dE1 certE1 checkE1

/-- The full derivation to the identity. -/
def certE : Certificate 1 := certE1 ++
  [ bwd "assoc" [Arg.c (Circuit.gate (Gate.t i0)), Arg.c (Circuit.gate (Gate.t i0)),
      Arg.c (Circuit.gate (Gate.z i0))] (afterG (Gate.s i0) Ctx.hole),
    fwd "tt" [Arg.q i0] (afterG (Gate.s i0) (beforeC (Circuit.gate (Gate.z i0)) Ctx.hole)),
    bwd "assoc" [Arg.c (Circuit.gate (Gate.s i0)), Arg.c (Circuit.gate (Gate.s i0)),
      Arg.c (Circuit.gate (Gate.z i0))] Ctx.hole,
    fwd "ss" [Arg.q i0] (beforeC (Circuit.gate (Gate.z i0)) Ctx.hole),
    fwd "zz" [Arg.q i0] Ctx.hole ]

theorem checkE : checkCertificate cE Circuit.one certE = true := by decide
theorem soundE : PhaseEquivalent cE Circuit.one := checkCertificate_sound cE Circuit.one certE checkE
theorem costE : (Cost.of cE).gateCount = 6 ∧ (Cost.of cE).tCount = 4 := by decide
theorem costE' : (Cost.of (Circuit.one : Circuit 1)).gateCount = 0 := by decide

/-! ### Examples F and G: X Z X Z needs a cost-neutral step -/

/-- X(0) ; Z(0) ; X(0) ; Z(0). -/
def cFG : Circuit 1 := seqGates [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]

/-- The derivation: commute the trailing X past the Z (cost-neutral, and *only* valid up to
global phase), re-associate so that the two Z become an adjacent pair, cancel them, drop the
identity, cancel the two X. -/
def certFG : Certificate 1 :=
  [ fwd "xz" [Arg.q i0] (afterG (Gate.x i0) (afterG (Gate.z i0) Ctx.hole)),
    bwd "assoc" [Arg.c (Circuit.gate (Gate.z i0)), Arg.c (Circuit.gate (Gate.z i0)),
      Arg.c (Circuit.gate (Gate.x i0))] (afterG (Gate.x i0) Ctx.hole),
    fwd "zz" [Arg.q i0] (afterG (Gate.x i0) (beforeC (Circuit.gate (Gate.x i0)) Ctx.hole)),
    fwd "idL" [Arg.c Circuit.one, Arg.c (Circuit.gate (Gate.x i0))]
      (afterG (Gate.x i0) Ctx.hole),
    fwd "xx" [Arg.q i0] Ctx.hole ]

theorem checkFG : checkCertificate cFG Circuit.one certFG = true := by decide
/-- Example G: X Z X Z is equivalent to the identity modulo global phase. -/
theorem soundFG : PhaseEquivalent cFG Circuit.one :=
  checkCertificate_sound cFG Circuit.one certFG checkFG
theorem costFG : (Cost.of cFG).gateCount = 4 := by decide

/-- The semantics of X Z X Z is exactly minus the identity: the global phase is -1, so the
circuit is phase-equivalent to the identity but *not* denotationally equal to it. -/
theorem ZXZX : Z2 * X2 * Z2 * X2 = (-1 : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z2, X2, mul2_apply]

/-- Embedding commutes with scalar multiplication: a global phase can be moved across the
embedding of a gate into the register. -/
theorem embed1_smulC {n : Nat} (z : ℂ) (U : Matrix Bool Bool ℂ) (i : Fin n) :
    embed1 (z • U) i = z • embed1 U i := by
  classical
  ext x y
  by_cases h : agreeOff [i] x y
  · simp [embed1_apply, h]
  · simp [embed1_apply, h]

theorem denotationFG : (denote cFG : Operator 1) = (-1 : ℂ) • 1 := by
  classical
  show embed1 Z2 i0 * embed1 X2 i0 * embed1 Z2 i0 * embed1 X2 i0 = (-1 : ℂ) • (1 : Operator 1)
  rw [embed1_mul, embed1_mul, embed1_mul, ZXZX, embed1_smulC, embed1_one]

theorem denotationFG_ne_one : (denote cFG : Operator 1) ≠ 1 := by
  classical
  intro h
  have h1 := congrFun (congrFun h (fun _ : Fin 1 => false)) (fun _ : Fin 1 => false)
  rw [denotationFG] at h1
  simp only [Matrix.one_apply, Pi.smul_apply] at h1
  norm_num at h1

/-- The equivalence of Example F/G is genuinely a *phase* equivalence: the two circuits do not
denote the same matrix. -/
theorem fg_not_exact : ¬ EqExact cFG (Circuit.one : Circuit 1) := by
  intro h
  have h1 := congrFun (congrFun h (fun _ : Fin 1 => false)) (fun _ : Fin 1 => false)
  rw [denotationFG, denote_one] at h1
  simp only [Matrix.one_apply, Pi.smul_apply] at h1
  norm_num at h1

/-- **The point of Example F.**  The explicitly defined greedy baseline - the first strictly
cost-decreasing one-step rewrite, repeatedly - cannot make progress on X Z X Z: no
cost-decreasing step exists, so it returns the circuit unchanged with four gates.  The
equality-saturation optimizer reaches the identity (zero gates) by first taking the
cost-neutral commutation step above. -/
theorem greedyStuckFG : Opt.greedy 10 cFG = cFG := by decide

/-- The greedy baseline leaves all four gates in place; the certificate above removes them
all. -/
theorem greedyCostFG : (Cost.of (Opt.greedy 10 cFG)).gateCount = 4 := by decide

/-- The greedy baseline is sound on this input (it just is not very good). -/
theorem greedySoundFG : PhaseEquivalent (Opt.greedy 10 cFG) cFG := Opt.greedy_phaseEquivalent 10 cFG
/-! ### Example H: T-count reduction -/

/-- T ; T ; T ; T on one qubit: four T gates. -/
def cH : Circuit 1 := seqGates [Gate.t i0, Gate.t i0, Gate.t i0, Gate.t i0]
/-- Four T gates reduce to a single Z, so the T-count drops from 4 to 0. -/
def dH : Circuit 1 := Circuit.gate (Gate.z i0)
def certH : Certificate 1 :=
  [ fwd "tt" [Arg.q i0] (afterG (Gate.t i0) (afterG (Gate.t i0) Ctx.hole)),
    bwd "assoc" [Arg.c (Circuit.gate (Gate.t i0)), Arg.c (Circuit.gate (Gate.t i0)),
      Arg.c (Circuit.gate (Gate.s i0))] Ctx.hole,
    fwd "tt" [Arg.q i0] (beforeC (Circuit.gate (Gate.s i0)) Ctx.hole),
    fwd "ss" [Arg.q i0] Ctx.hole ]
theorem checkH : checkCertificate cH dH certH = true := by decide
theorem soundH : PhaseEquivalent cH dH := checkCertificate_sound cH dH certH checkH
theorem costH_in : (Cost.of cH).tCount = 4 := by decide
theorem costH_out : (Cost.of dH).tCount = 0 := by decide

/-! ### Example I: two-qubit gate reduction across a disjoint gate -/

/-- CNOT(0,1) ; X(2) ; CNOT(0,1) on three qubits. -/
def cI : Circuit 3 := seqGates [cx3, Gate.x k2, cx3]
/-- X(2): commuting the single-qubit gate past the CNOT exposes the CNOT cancellation. -/
def dI : Circuit 3 := Circuit.gate (Gate.x k2)
def certI : Certificate 3 :=
  [ fwd "disjoint" [Arg.g (Gate.x k2), Arg.g cx3] (afterG cx3 Ctx.hole),
    bwd "assoc" [Arg.c (Circuit.gate cx3), Arg.c (Circuit.gate cx3),
      Arg.c (Circuit.gate (Gate.x k2))] Ctx.hole,
    fwd "cxcx" [Arg.q k0, Arg.q k1] (beforeC (Circuit.gate (Gate.x k2)) Ctx.hole),
    fwd "idL" [Arg.c Circuit.one, Arg.c (Circuit.gate (Gate.x k2))] Ctx.hole ]
theorem checkI : checkCertificate cI dI certI = true := by decide
theorem soundI : PhaseEquivalent cI dI := checkCertificate_sound cI dI certI checkI
theorem costI_in : (Cost.of cI).twoQubitCount = 2 := by decide
theorem costI_out : (Cost.of dI).twoQubitCount = 0 := by decide

/-! ### Example J: uncomputation of a whole circuit (dead-code elimination) -/

/-- A three-gate block. -/
def workJ : Circuit 2 := seqGates [Gate.h j0, Gate.cx j0 j1 (by decide), Gate.s j1]

/-- The block followed by its own uncomputation. -/
def cJ : Circuit 2 := Circuit.seq workJ (Circuit.inv workJ)
def certJ : Certificate 2 :=
  [fwd "uncompute2" [Arg.c workJ, Arg.c (Circuit.inv workJ)] Ctx.hole]
theorem checkJ : checkCertificate cJ Circuit.one certJ = true := by decide
theorem soundJ : PhaseEquivalent cJ Circuit.one := checkCertificate_sound cJ Circuit.one certJ checkJ
/-- The uncomputation law is an *exact* matrix identity, not merely a phase equivalence. -/
theorem exactJ : EqExact cJ Circuit.one := denote_inv_mul workJ

end Examples
end Quantum
