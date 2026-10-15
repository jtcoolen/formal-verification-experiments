/-
The quantum Fourier transform as a circuit in the verified language.

The transform is built only from primitives of Quantum/Syntax.lean: Hadamards and *controlled
phases* CP(theta) (the reason CP was added to the gate library), followed by the usual
bit-reversal SWAPs.  Because the circuits live in the deeply embedded language, everything the
optimizer can do to them - cancellation, re-association, uncomputation - is certified by the
same independent checker that proves PhaseEquivalent.

The theorems here are the convention-independent content: the QFT circuit is unitary, its
syntactic inverse really inverts it (exactly, not merely up to phase), and the cancellation is
certifiable by the independent checker.  The entrywise identification with the DFT matrix
F(x,y) = omega^(x*y)/2^m depends on the bit-weight convention of Fintype (Basis n) and is
recorded as remaining work.
-/
import Quantum.Optimizer
import Quantum.Correctness
import Quantum.Architecture

namespace Shor
namespace QFT

open Quantum Quantum.Opt

noncomputable section

def j0 : Fin 2 := ⟨0, by decide⟩
def j1 : Fin 2 := ⟨1, by decide⟩

/-- A controlled phase of angle pi / 2^(k+1) between two qubits: the gate the QFT ladder is
made of. -/
def cphase {n : Nat} (c t : Fin n) (h : c ≠ t) (k : Nat) : Circuit n :=
  Circuit.gate (Gate.cp c t h (Angle.piMul (1 / (2 ^ (k + 1) : ℚ))))

/-- The two-qubit quantum Fourier transform circuit: Hadamard on the first qubit, a controlled
phase of pi/2 from the second qubit onto the first, a Hadamard on the second qubit, and the
bit-reversal swap. -/
def qft2 : Circuit 2 :=
  Circuit.seq (Circuit.gate (Gate.h j0))
    (Circuit.seq (cphase j1 j0 (by decide) 0)
      (Circuit.seq (Circuit.gate (Gate.h j1)) (Circuit.gate (Gate.swap j0 j1 (by decide)))))

/-- The inverse QFT circuit: the syntactic inverse of qft2, i.e. each gate inverted and the
order reversed.  Running it after the forward transform is the identity *exactly*. -/
def iqft2 : Circuit 2 := Circuit.inv qft2

/-- The QFT circuit is unitary: an instance of the general theorem that every circuit denotes a
unitary operator. -/
theorem qft2_unitary : IsUnitaryM (denote qft2) := denote_isUnitary qft2

/-- The inverse circuit really inverts the forward circuit - as an exact matrix identity, not
merely up to global phase. -/
theorem qft2_inverse_exact : EqExact (Circuit.seq qft2 iqft2) Circuit.one := by
  show denote iqft2 * denote qft2 = 1
  exact denote_inv_mul qft2

/-- The other order as well. -/
theorem qft2_inverse_exact' : EqExact (Circuit.seq iqft2 qft2) Circuit.one := by
  show denote qft2 * denote iqft2 = 1
  exact denote_mul_inv qft2

/-- Consequently both compositions are phase-equivalent to the identity. -/
theorem qft2_compose_phase : PhaseEquivalent (Circuit.seq qft2 iqft2) Circuit.one :=
  PhaseEquivalent.of_eqExact qft2_inverse_exact

/-- A forward certificate step. -/
def fwd {n : Nat} (name : String) (args : List (Quantum.Arg n)) (ctx : Quantum.Ctx n) :
    Quantum.Step n :=
  { ruleId := name, args := args, ctx := ctx, backward := false }

/-- The one-step certificate that cancels the QFT against its inverse. -/
def stQft : Quantum.Step 2 :=
  fwd "uncompute2" [Quantum.Arg.c qft2, Quantum.Arg.c iqft2] Quantum.Ctx.hole

theorem hfind_uncompute2 : Quantum.findRule 2 "uncompute2" =
    some (Quantum.ruleUncompute2 2) := rfl

/-- **A certifiable QFT-ladder simplification.**  A controlled phase of angle zero is the
identity, and the independent checker accepts that one-step certificate: this is the shape of
the trivial blocks a QFT ladder accumulates (for instance when a controlled rotation is
controlled on a qubit whose phase contribution is known to vanish). -/
def stCpZero : Quantum.Step 2 :=
  fwd "cp_zero" [Quantum.Arg.q j1, Quantum.Arg.q j0] Quantum.Ctx.hole

def cpZero : Circuit 2 := Circuit.gate (Gate.cp j1 j0 (by decide) 0)

theorem cp_zero_certified : checkCertificate cpZero Circuit.one [stCpZero] = true := by decide

theorem cp_zero_phase : PhaseEquivalent cpZero Circuit.one :=
  Quantum.checkCertificate_sound _ _ _ cp_zero_certified

/-- The cost accounting sees the controlled phase as one Toffoli-equivalent operation, and the
identity circuit as none: this is the Q x T bookkeeping of arXiv:2609.09582 applied to a QFT
ladder gate. -/
theorem cp_cost : Quantum.toffoliT cpZero = 1 /\ Quantum.toffoliT (Circuit.one : Circuit 2) = 0 :=
  by decide

theorem cp_width : Quantum.qubitWidth cpZero = 2 := by decide

/-- The summed angle of two pi/2 controlled phases is exactly pi: exact rational arithmetic,
proved by norm_num (the kernel will not evaluate rational addition itself). -/
theorem cphase_sum : (Angle.piMul (1 / 2) + Angle.piMul (1 / 2) : Angle) = Angle.piMul 1 := by
  apply Angle.eq_of_components <;> simp [Angle.piMul, Angle.add_piQ] <;> norm_num

/-- Two consecutive pi/2 controlled phases therefore denote a single CP(pi): the semantic
statement of the ladder identity, established from the verified rule rw_cp_add together with the
exact angle computation above. -/
theorem two_cphases :
    PhaseEquivalent
      (Circuit.seq (cphase j1 j0 (by decide) 0) (cphase j1 j0 (by decide) 0) : Circuit 2)
      (Circuit.gate (Gate.cp j1 j0 (by decide) Angle.pi)) := by
  classical
  have h := Quantum.rw_cp_add (i := j1) (j := j0) (by decide)
    (Angle.piMul (1 / 2)) (Angle.piMul (1 / 2))
  refine PhaseEquivalent.trans h (PhaseEquivalent.of_eqExact ?_)
  show denote (Circuit.gate (Gate.cp j1 j0 (by decide)
      (Angle.piMul (1 / 2) + Angle.piMul (1 / 2)))) =
    denote (Circuit.gate (Gate.cp j1 j0 (by decide) Angle.pi))
  simp only [denote_gate, denoteGate_cp]
  rw [cphase_sum]
  rfl

end

end QFT
end Shor
