/-
End-to-end correctness of the public optimizer.

This module contains the *external* verification boundary: the optimizer is untrusted, and
the only thing that makes its answer a proof is the independent certificate checker of
Quantum/Certificates.lean.  The central result is `Opt.optimize_sound`: whenever the public
API returns a circuit and a certificate, the checker accepts that certificate, and therefore
the two circuits denote the same unitary up to a complex scalar of unit modulus.
-/
import Quantum.Optimizer

namespace Quantum
namespace Opt

open LambdaSat EG

/-! ### The fail-closed final gate -/

/-- The empty certificate is always accepted: every circuit is phase-equivalent to itself. -/
theorem checkCertificate_refl {n : Nat} (c : Circuit n) : checkCertificate c c [] = true := by
  classical
  show (match walk c [] with | some b' => decide (b' = c) | none => false) = true
  rw [walk_nil]
  simp

/-- When the checker accepts a candidate, `finish` returns it unchanged. -/
theorem finish_accepted {n : Nat} {c c' : Circuit n} (cert : Certificate n)
    (h : checkCertificate c c' cert = true) : finish c c' cert = (c', cert) := by
  classical
  simp only [finish, h, if_pos, reduceCtorEq]
  split <;> simp_all

/-- When the checker rejects a candidate, `finish` falls back to the input circuit with the
empty (reflexive) certificate. -/
theorem finish_rejected {n : Nat} {c c' : Circuit n} (cert : Certificate n)
    (h : checkCertificate c c' cert = false) : finish c c' cert = (c, []) := by
  classical
  simp [finish, h]

/-- **Soundness of the final gate.** Whatever candidate the optimizer hands to `finish`, the
result it produces is a circuit whose certificate the independent checker accepts, and which
is therefore phase-equivalent to the input.  If the candidate certificate is rejected, the
input circuit itself is returned with the reflexive certificate: the optimizer fails closed. -/
theorem finish_spec {n : Nat} (c c' : Circuit n) (cert : Certificate n) :
    checkCertificate c (finish c c' cert).1 (finish c c' cert).2 = true ∧
      PhaseEquivalent c (finish c c' cert).1 := by
  classical
  by_cases h : checkCertificate c c' cert
  · rw [finish_accepted (c := c) (c' := c') cert h]
    exact ⟨h, checkCertificate_sound c c' cert h⟩
  · rw [finish_rejected (c := c) (c' := c') cert (by simpa using h)]
    exact ⟨checkCertificate_refl c, PhaseEquivalent.refl c⟩

/-! ### Branch equations of the optimizer body -/

theorem optimizeFrom_none {n : Nat} (cfg : Config) (c : Circuit n)
    (h : (extractAuto (saturatedGraph cfg c) (rootOf cfg c) : Option (Circuit n)) = none) :
    optimizeFrom cfg c = some (finish c c []) := by
  classical
  simp only [optimizeFrom, h]

theorem optimizeFrom_found {n : Nat} (cfg : Config) (c x : Circuit n) (y : Certificate n)
    (h : (extractAuto (saturatedGraph cfg c) (rootOf cfg c) : Option (Circuit n)) = some x)
    (h2 : findDerivationCost cfg c x = some y) :
    optimizeFrom cfg c = some (finish c x y) := by
  classical
  simp only [optimizeFrom, h, h2]

theorem optimizeFrom_notFound {n : Nat} (cfg : Config) (c x : Circuit n)
    (h : (extractAuto (saturatedGraph cfg c) (rootOf cfg c) : Option (Circuit n)) = some x)
    (h2 : findDerivationCost cfg c x = none) :
    optimizeFrom cfg c = some (finish c c []) := by
  classical
  simp only [optimizeFrom, h, h2]

/-- Every branch of the optimizer body produces a `finish`ed result, so every branch is
sound.  This is the case analysis that makes the end-to-end theorem below go through without
trusting saturation, e-matching, congruence, extraction or the search. -/
theorem optimizeFrom_spec {n : Nat} (cfg : Config) (c : Circuit n)
    (p : Circuit n × Certificate n) (h : optimizeFrom cfg c = some p) :
    checkCertificate c p.1 p.2 = true ∧ PhaseEquivalent c p.1 := by
  classical
  rcases h1 : (extractAuto (saturatedGraph cfg c) (rootOf cfg c) : Option (Circuit n)) with _ | x
  · rw [optimizeFrom_none cfg c h1] at h
    have hp : p = finish c c [] := (Option.some.inj h).symm
    rw [hp]
    exact finish_spec c c []
  · rcases h2 : findDerivationCost cfg c x with _ | y
    · rw [optimizeFrom_notFound cfg c x h1 h2] at h
      have hp : p = finish c c [] := (Option.some.inj h).symm
      rw [hp]
      exact finish_spec c c []
    · rw [optimizeFrom_found cfg c x y h1 h2] at h
      have hp : p = finish c x y := (Option.some.inj h).symm
      rw [hp]
      exact finish_spec c x y

/-- **END-TO-END SOUNDNESS OF THE PUBLIC OPTIMIZER.**

If \`optimize cfg c = some (c', cert)\` then
  1. the independent checker accepts the certificate: \`checkCertificate c c' cert = true\`, and
  2. the circuits are equivalent modulo global phase: \`PhaseEquivalent c c'\`,
where the second follows from the first by the checker soundness theorem
(\`checkCertificate_sound\`), which depends only on syntax, semantics, the verified rewrite
library and proved contextual congruence - never on the optimizer. -/
theorem optimize_sound {n : Nat} (cfg : Config) (c c' : Circuit n) (cert : Certificate n)
    (h : optimize cfg c = some (c', cert)) :
    checkCertificate c c' cert = true ∧ PhaseEquivalent c c' := by
  classical
  rw [optimize_eq] at h
  exact optimizeFrom_spec cfg c (c', cert) h

/-- The optimizer never fails: it always returns a circuit with an accepted certificate
(possibly the input circuit with the empty certificate).  Termination is not a theorem here
but a fact about the definitions: every loop (\`saturateF\`, \`computeCostsF\`, \`extractF\`,
\`findDerivation\`, \`greedy\`) is structural or fuel-bounded, so Lean has already checked that
they terminate on every input. -/
theorem optimize_isSome {n : Nat} (cfg : Config) (c : Circuit n) :
    (optimize cfg c).isSome = true := by
  classical
  rw [optimize_eq]
  rcases h1 : (extractAuto (saturatedGraph cfg c) (rootOf cfg c) : Option (Circuit n)) with _ | x
  · rw [optimizeFrom_none cfg c h1]; simp
  · rcases h2 : findDerivationCost cfg c x with _ | y
    · rw [optimizeFrom_notFound cfg c x h1 h2]; simp
    · rw [optimizeFrom_found cfg c x y h1 h2]; simp

end Opt
end Quantum
