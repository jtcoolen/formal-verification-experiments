/-
Adversarial regression suite.

The documented failure modes of real quantum compilers (see
KB/papers/quantum-compiler-bugs.md, pinned to commit 8391022 of
barghouthi/quantum-optimizer-bugs) encoded as kernel-checked Lean propositions.

Two kinds of test appear here:
  * positive: on inputs that break floating-point compilers, this optimizer produces a result
    whose certificate the independent checker accepts, and the result is the *right* one;
  * negative: tampered certificates, illegal positions, wrong qubit indices, wrong angle
    signs, broken derivation chains, tampered endpoints and unsupported rewrites, each of
    which the checker must reject.

Note on `decide`: the kernel does not reduce `Rat.add`, so a certificate whose claimed circuit
contains an *unevaluated* angle sum cannot be checked by `decide`.  Those certificates are
instead proved accepted by `step_of` / `walk_cons_ok` / `checkCertificate_of_walk`, which
match circuits syntactically against the recomputed left-hand side and never evaluate a
rational number.  Everything else is discharged by `decide` - never by `native_decide`, and
never by `#eval`.
-/
import Quantum.Correctness
import Quantum.ControlPhase
import Quantum.Examples

set_option maxHeartbeats 8000000

namespace Quantum
namespace BugRegression

open Classical Opt

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

def fwd {n : Nat} (name : String) (args : List (Arg n)) (ctx : Ctx n) : Step n :=
  { ruleId := name, args := args, ctx := ctx, backward := false }

def bwd {n : Nat} (name : String) (args : List (Arg n)) (ctx : Ctx n) : Step n :=
  { ruleId := name, args := args, ctx := ctx, backward := true }

/-- The hole sits after the gate `g`. -/
def afterG {n : Nat} (g : Gate n) : Ctx n -> Ctx n := fun k => Ctx.seqL (Circuit.gate g) k

/-- The hole sits before the gate `g`. -/
def beforeG {n : Nat} (g : Gate n) : Ctx n -> Ctx n := fun k => Ctx.seqR k (Circuit.gate g)

/-! ### Rule handles -/

/-- The library rule that fuses two rotations on the same qubit. -/
def rzAddRule (n : Nat) : Rule n := ruleAddRot (n := n) Gate.rz "rz_add" rw_rz_add

theorem hfind_rz_add {n : Nat} : findRule n "rz_add" = some (rzAddRule n) := rfl

/-! ### 1. Large-angle cancellation (Qiskit, PennyLane, Cirq, Qrisp, CUDA-Q, quilc) -/

/-- `Rz(10^17) ; Rz(pi) ; Rz(-10^17)`.  A floating-point compiler computes `10^17 + pi`,
rounds it back to `10^17`, cancels against `-10^17` and reports the identity.  Angles here are
pairs of arbitrary-precision rationals, so the sum is exactly `pi`. -/
def big : Angle := ⟨100000000000000000, 0⟩
def c1 : Circuit 1 := sg [Gate.rz i0 big, Gate.rz i0 Angle.pi, Gate.rz i0 (-big)]

theorem angle_sum_exact : big + (Angle.pi + (-big)) = Angle.pi := by
  apply Angle.eq_of_components <;>
    simp only [Angle.add_rat, Angle.add_piQ, Angle.neg_rat, Angle.neg_piQ, big, Angle.pi,
      Angle.piMul, Angle.zero_rat, Angle.zero_piQ] <;> norm_num

/-- The intermediate circuit after fusing the trailing pair, and after fusing the leading gate. -/
def c1a : Circuit 1 := Circuit.seq (Circuit.gate (Gate.rz i0 big))
  (Circuit.gate (Gate.rz i0 (Angle.pi + (-big))))

def c1b : Circuit 1 := Circuit.gate (Gate.rz i0 (big + (Angle.pi + (-big))))

def s1 : Step 1 :=
  fwd "rz_add" [Arg.q i0, Arg.a Angle.pi, Arg.a (-big)] (afterG (Gate.rz i0 big) Ctx.hole)

def s2 : Step 1 := fwd "rz_add" [Arg.q i0, Arg.a big, Arg.a (Angle.pi + (-big))] Ctx.hole

theorem c1_walk : walk c1 [s1, s2] = some c1b := by
  classical
  refine walk_cons_ok c1 c1a c1b s1 [s2] ?_ ?_
  · exact step_of c1 c1a s1 (rzAddRule 1) hfind_rz_add rfl rfl rfl
  · refine walk_cons_ok c1a c1b c1b s2 [] ?_ (walk_nil c1b)
    exact step_of c1a c1b s2 (rzAddRule 1) hfind_rz_add rfl rfl rfl

/-- The certificate is accepted by the independent checker. -/
theorem c1_fuses : checkCertificate c1 c1b [s1, s2] = true :=
  checkCertificate_of_walk c1 c1b [s1, s2] c1_walk

theorem c1_sound : PhaseEquivalent c1 c1b := checkCertificate_sound c1 c1b [s1, s2] c1_fuses

/-- The fused angle denotes exactly pi: no rounding, no loss of the middle rotation. -/
theorem c1_angle_val : Angle.val (big + (Angle.pi + (-big))) = Angle.val Angle.pi :=
  Angle.val_congr angle_sum_exact

/-- Therefore the three-gate circuit is phase-equivalent to Rz(pi), and hence to Z - which is
what the buggy compilers *should* have produced, and *not* the identity. -/
theorem c1_equiv_rz_pi : PhaseEquivalent c1 (Circuit.gate (Gate.rz i0 Angle.pi)) := by
  classical
  refine PhaseEquivalent.trans (b := c1b) c1_sound (PhaseEquivalent.of_eqExact ?_)
  show denote (Circuit.gate (Gate.rz i0 (big + (Angle.pi + (-big))))) =
    denote (Circuit.gate (Gate.rz i0 Angle.pi))
  simp only [denote_gate, denoteGate_rz, c1_angle_val]

theorem c1_to_z : PhaseEquivalent c1 (Circuit.gate (Gate.z i0)) :=
  PhaseEquivalent.trans c1_equiv_rz_pi (rw_rz_pi_z i0)

/-- Whatever the optimizer returns for this circuit comes with an accepted certificate. -/
theorem c1_optimizer_certified (p : Circuit 1 × Certificate 1)
    (h : optimize Config.default c1 = some p) :
    checkCertificate c1 p.1 p.2 = true ∧ PhaseEquivalent c1 p.1 :=
  optimize_sound Config.default c1 p.1 p.2 h

/-! ### 2. Overflow-resistant rational phases (QuiZX) -/

/-- The QuiZX pair: both angles are near `pi/2`, the denominators are coprime and their
product is `2^64 - 1`, which overflows fixed-width 64-bit rational addition. -/
def qA : Angle := ⟨0, (2147483647 : ℚ) / 4294967295⟩
def qB : Angle := ⟨0, (2147483648 : ℚ) / 4294967297⟩

theorem qsum_ne_zero : qA + qB ≠ 0 := by
  intro h
  have := congrArg Angle.piQ h
  simp only [Angle.add_piQ, qA, qB, Angle.zero_piQ] at this
  norm_num at this

theorem q_fuse_walk : walk (sg [Gate.rz i0 qA, Gate.rz i0 qB] : Circuit 1)
    [fwd "rz_add" [Arg.q i0, Arg.a qA, Arg.a qB] Ctx.hole] =
    some (Circuit.gate (Gate.rz i0 (qA + qB))) := by
  classical
  exact walk_cons_ok _ _ _ _ [] (step_of _ _ _ (rzAddRule 1) hfind_rz_add rfl rfl rfl)
    (walk_nil _)

theorem q_fuse :
    checkCertificate (sg [Gate.rz i0 qA, Gate.rz i0 qB] : Circuit 1)
      (Circuit.gate (Gate.rz i0 (qA + qB)))
      [fwd "rz_add" [Arg.q i0, Arg.a qA, Arg.a qB] Ctx.hole] = true := by
  classical
  exact checkCertificate_of_walk _ _ _ q_fuse_walk

theorem q_sound : PhaseEquivalent (sg [Gate.rz i0 qA, Gate.rz i0 qB] : Circuit 1)
    (Circuit.gate (Gate.rz i0 (qA + qB))) :=
  checkCertificate_sound _ _ _ q_fuse

/-! ### 3. Controlled global phase -/

/-- `Rz(2π) ≈ I` (global phase `-1`): a legitimate phase rewrite. -/
theorem rz_twoPi_ok :
    checkCertificate (sg [Gate.rz i0 Angle.twoPi] : Circuit 1) Circuit.one
      [fwd "rz_twoPi_one" [Arg.q i0] Ctx.hole] = true := by decide

/-- `CRz(2π) ≈ I` is FALSE: under a control the phase becomes a relative phase.  There is no
rule that performs this simplification, and a certificate that pretends there is gets refused. -/
theorem crz_twoPi_certificate_rejected :
    checkCertificate (sg [Gate.crz j0 j1 (by decide) Angle.twoPi] : Circuit 2) Circuit.one
      [fwd "rz_twoPi_one" [Arg.q j0] Ctx.hole] = false := by decide

theorem crz_twoPi_not_id : ¬ PhaseEquivalent
    (Circuit.gate (Gate.crz j0 j1 (by decide) Angle.twoPi) : Circuit 2) Circuit.one :=
  ControlPhase.crz_twoPi_not_phase_one (by decide)

/-- `CRz(0)` *is* the identity, and the library has exactly that rule. -/
theorem crz_zero_ok :
    checkCertificate (sg [Gate.crz j0 j1 (by decide) 0] : Circuit 2) Circuit.one
      [fwd "crz_zero" [Arg.q j0, Arg.q j1] Ctx.hole] = true := by decide

/-! ### 4. Qubit permutation and wire order -/

/-- Moving an operator to a different wire is not a valid optimization. -/
theorem wire_permutation_rejected :
    checkCertificate (sg [Gate.x j0, Gate.z j1] : Circuit 2) (sg [Gate.x j1, Gate.z j0])
      [fwd "disjoint" [Arg.g (Gate.x j0), Arg.g (Gate.z j1)] Ctx.hole] = false := by decide

/-- Exchanging CNOT control and target changes the unitary, and the checker refuses a
certificate whose claimed output has the wires exchanged. -/
theorem cx_wire_order_rejected :
    checkCertificate (sg [Gate.cx j0 j1 (by decide)] : Circuit 2)
      (sg [Gate.cx j1 j0 (by decide)])
      [fwd "cxcx" [Arg.q j0, Arg.q j1] Ctx.hole] = false := by decide

/-! ### 5. Unsupported gates are never silently replaced -/

theorem unknown_rule_rejected :
    checkCertificate (sg [Gate.h i0, Gate.h i0] : Circuit 1) Circuit.one
      [fwd "toffoli_cancel" [Arg.q i0] Ctx.hole] = false := by decide

theorem bogus_decomposition_rejected :
    checkCertificate (sg [Gate.crz j0 j1 (by decide) Angle.pi] : Circuit 2)
      (sg [Gate.cx j0 j1 (by decide)] : Circuit 2)
      [fwd "crz_to_cx" [Arg.q j0, Arg.q j1, Arg.a Angle.pi] Ctx.hole] = false := by decide

/-! ### 6. Small-angle accumulation -/

/-- One hundred rotations by `pi/100` fuse into exactly `pi`.  A tolerance-based pass that
deletes "small" gates would destroy the total effect. -/
def small : Angle := Angle.piMul (1 / 100)

theorem small_sum_exact : (100 : ℚ) • small = Angle.pi := by
  apply Angle.eq_of_components <;> simp [Angle.smulRat, small, Angle.piMul, Angle.pi]

theorem small_not_zero : small ≠ 0 := by
  intro h
  have := congrArg Angle.piQ h
  simp only [Angle.piMul, small, Angle.zero_piQ] at this
  norm_num at this

/-! ### 7. Numerically close but distinct angles are not inverses -/

def a1 : Angle := Angle.piMul (1/4)
def a2 : Angle := Angle.piMul (1/4) + ⟨1/1000000000, 0⟩

theorem close_angles_distinct : a1 ≠ -a2 := by
  intro h
  have := congrArg Angle.piQ h
  simp only [a1, a2, Angle.add_piQ, Angle.neg_piQ, Angle.piMul, Angle.zero_piQ] at this
  norm_num at this

/-! ### 8-13. Structural tampering with a valid derivation -/

def cXZXZ : Circuit 1 := sg [Gate.x i0, Gate.z i0, Gate.x i0, Gate.z i0]

theorem valid_fg : checkCertificate cXZXZ Circuit.one Examples.certFG = true :=
  Examples.checkFG

theorem reordered_rejected :
    checkCertificate cXZXZ Circuit.one Examples.certFG.reverse = false := by decide

theorem missing_step_rejected :
    checkCertificate cXZXZ Circuit.one
      (Examples.certFG.take 2 ++ Examples.certFG.drop 3) = false := by decide

theorem wrong_endpoint_rejected :
    checkCertificate cXZXZ (sg [Gate.x i0] : Circuit 1) Examples.certFG = false := by decide

theorem wrong_start_rejected :
    checkCertificate (sg [Gate.x i0, Gate.x i0] : Circuit 1) Circuit.one Examples.certFG =
    false := by decide

theorem wrong_position_rejected :
    checkCertificate cXZXZ Circuit.one
      [fwd "xx" [Arg.q i0] (afterG (Gate.x i0) Ctx.hole)] = false := by decide

/-- The commutation rule's side condition really is checked: two gates on the *same* qubit are
not disjoint, so the rule does not fire (the certificate-level analogue of an unjustified
e-graph merge). -/
theorem disjoint_side_condition :
    checkCertificate (sg [Gate.x i0, Gate.z i0] : Circuit 1)
      (sg [Gate.z i0, Gate.x i0])
      [fwd "disjoint" [Arg.g (Gate.x i0), Arg.g (Gate.z i0)] Ctx.hole] = false := by decide

theorem tampered_extraction_rejected :
    checkCertificate (sg [Gate.t i0, Gate.t i0, Gate.s i0] : Circuit 1) Circuit.one
      Examples.certFG = false := by decide

theorem unrelated_cheaper_output_rejected :
    checkCertificate (sg [Gate.h i0, Gate.s i0] : Circuit 1) Circuit.one Examples.certFG =
    false := by decide

/-- A *valid* step of a derivation, applied to a circuit it does not match, is refused: the
checker recomputes the left-hand side instead of trusting a proposed replacement. -/
theorem recomputed_lhs_not_trusted :
    checkCertificate (sg [Gate.s i0, Gate.s i0] : Circuit 1) Circuit.one Examples.certFG =
    false := by decide

/-! ### 14. Cost model agrees with the returned implementation -/

theorem cost_two_qubit :
    (Cost.of (sg [Gate.cx j0 j1 (by decide), Gate.t j0] : Circuit 2)).twoQubitCount = 1 :=
  by decide

theorem cost_tcount :
    (Cost.of (sg [Gate.t i0, Gate.tDag i0, Gate.s i0] : Circuit 1)).tCount = 2 := by decide

theorem cost_identity_zero : (Cost.of (Circuit.one : Circuit 1)).gateCount = 0 := by decide

theorem cost_additive (gs hs : List (Gate 1)) :
    Cost.ofGates (gs ++ hs) = Cost.ofGates gs + Cost.ofGates hs := Cost.ofGates_append gs hs

end BugRegression
end Quantum
